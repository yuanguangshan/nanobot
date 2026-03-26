"""Personal WeChat (微信) channel using HTTP long-poll API.

Uses the ilinkai.weixin.qq.com API for personal WeChat messaging.
No WebSocket, no local WeChat client needed — just HTTP requests with a
bot token obtained via QR code login.

Protocol reverse-engineered from ``@tencent-weixin/openclaw-weixin`` v1.0.2.
Enhanced with Production-grade fixes (Session Guard, Context Persistence, CDN Retry, Markdown Strip).
"""

from __future__ import annotations

import asyncio
import base64
import hashlib
import io
import json
import os
import re
import time
import uuid
import wave
from collections import OrderedDict
from pathlib import Path
from typing import Any
from urllib.parse import quote

import httpx
from loguru import logger
from pydantic import Field

from nanobot.bus.events import OutboundMessage
from nanobot.bus.queue import MessageBus
from nanobot.channels.base import BaseChannel
from nanobot.config.paths import get_media_dir, get_runtime_subdir
from nanobot.config.schema import Base
from nanobot.utils.helpers import split_message

# ---------------------------------------------------------------------------
# Protocol constants
# ---------------------------------------------------------------------------

ITEM_TEXT = 1
ITEM_IMAGE = 2
ITEM_VOICE = 3
ITEM_FILE = 4
ITEM_VIDEO = 5

MESSAGE_TYPE_USER = 1
MESSAGE_TYPE_BOT = 2
MESSAGE_STATE_FINISH = 2

WEIXIN_MAX_MESSAGE_LEN = 4000
BASE_INFO: dict[str, str] = {"channel_version": "1.0.2"}

ERRCODE_SESSION_EXPIRED = -14
MAX_CONSECUTIVE_FAILURES = 3
BACKOFF_DELAY_S = 30
RETRY_DELAY_S = 2
DEFAULT_LONG_POLL_TIMEOUT_S = 35

UPLOAD_MEDIA_IMAGE = 1
UPLOAD_MEDIA_VIDEO = 2
UPLOAD_MEDIA_FILE = 3

_IMAGE_EXTS = {".jpg", ".jpeg", ".png", ".gif", ".bmp", ".webp", ".tiff", ".ico", ".svg"}
_VIDEO_EXTS = {".mp4", ".avi", ".mov", ".mkv", ".webm", ".flv"}


class WeixinConfig(Base):
    """Personal WeChat channel configuration."""
    enabled: bool = False
    allow_from: list[str] = Field(default_factory=list)
    base_url: str = "https://ilinkai.weixin.qq.com"
    cdn_base_url: str = "https://novac2c.cdn.weixin.qq.com/c2c"
    token: str = ""
    state_dir: str = ""
    poll_timeout: int = DEFAULT_LONG_POLL_TIMEOUT_S


class WeixinChannel(BaseChannel):
    name = "weixin"
    display_name = "WeChat"

    @classmethod
    def default_config(cls) -> dict[str, Any]:
        return WeixinConfig().model_dump(by_alias=True)

    def __init__(self, config: Any, bus: MessageBus):
        if isinstance(config, dict):
            config = WeixinConfig.model_validate(config)
        super().__init__(config, bus)
        self.config: WeixinConfig = config

        self._client: httpx.AsyncClient | None = None
        self._get_updates_buf: str = ""
        self._context_tokens: dict[str, str] = {}  # 持久化上下文Token
        self._session_paused_until: float = 0.0    # 熔断时间戳 (Session Guard)
        self._processed_ids: OrderedDict[str, None] = OrderedDict()
        self._state_dir: Path | None = None
        self._token: str = ""
        self._poll_task: asyncio.Task | None = None
        self._next_poll_timeout_s: int = DEFAULT_LONG_POLL_TIMEOUT_S

    # ------------------------------------------------------------------
    # State persistence (增强：保存 context_tokens 和 session 熔断状态)
    # ------------------------------------------------------------------
    def _get_state_dir(self) -> Path:
        if self._state_dir:
            return self._state_dir
        if self.config.state_dir:
            d = Path(self.config.state_dir).expanduser()
        else:
            d = get_runtime_subdir("weixin")
        d.mkdir(parents=True, exist_ok=True)
        self._state_dir = d
        return d

    def _load_state(self) -> bool:
        state_file = self._get_state_dir() / "account.json"
        if not state_file.exists():
            return False
        try:
            data = json.loads(state_file.read_text())
            self._token = data.get("token", "")
            self._get_updates_buf = data.get("get_updates_buf", "")
            self._context_tokens = data.get("context_tokens", {})
            self._session_paused_until = data.get("session_paused_until", 0.0)
            base_url = data.get("base_url", "")
            if base_url:
                self.config.base_url = base_url
            return bool(self._token)
        except Exception as e:
            logger.warning("Failed to load WeChat state: {}", e)
            return False

    def _save_state(self) -> None:
        state_file = self._get_state_dir() / "account.json"
        try:
            data = {
                "token": self._token,
                "get_updates_buf": self._get_updates_buf,
                "base_url": self.config.base_url,
                "context_tokens": self._context_tokens,
                "session_paused_until": self._session_paused_until,
            }
            state_file.write_text(json.dumps(data, ensure_ascii=False))
        except Exception as e:
            logger.warning("Failed to save WeChat state: {}", e)

    # ------------------------------------------------------------------
    # HTTP helpers
    # ------------------------------------------------------------------
    @staticmethod
    def _random_wechat_uin() -> str:
        uint32 = int.from_bytes(os.urandom(4), "big")
        return base64.b64encode(str(uint32).encode()).decode()

    def _make_headers(self, *, auth: bool = True) -> dict[str, str]:
        headers: dict[str, str] = {
            "X-WECHAT-UIN": self._random_wechat_uin(),
            "Content-Type": "application/json",
            "AuthorizationType": "ilink_bot_token",
        }
        if auth and self._token:
            headers["Authorization"] = f"Bearer {self._token}"
        return headers

    async def _api_get(self, endpoint: str, params: dict | None = None, *, auth: bool = True, extra_headers: dict[str, str] | None = None) -> dict:
        assert self._client is not None
        url = f"{self.config.base_url}/{endpoint}"
        hdrs = self._make_headers(auth=auth)
        if extra_headers:
            hdrs.update(extra_headers)
        resp = await self._client.get(url, params=params, headers=hdrs)
        resp.raise_for_status()
        return resp.json()

    async def _api_post(self, endpoint: str, body: dict | None = None, *, auth: bool = True) -> dict:
        assert self._client is not None
        url = f"{self.config.base_url}/{endpoint}"
        payload = body or {}
        if "base_info" not in payload:
            payload["base_info"] = BASE_INFO
        resp = await self._client.post(url, json=payload, headers=self._make_headers(auth=auth))
        resp.raise_for_status()
        return resp.json()

    # ------------------------------------------------------------------
    # Markdown Stripper (新增：清洗AI文本，防止微信端显示错乱)
    # ------------------------------------------------------------------
    @staticmethod
    def _markdown_to_plain_text(text: str) -> str:
        # Strip code block fences but keep content
        text = re.sub(r"```[^\n]*\n?(.*?)```", r"\1", text, flags=re.DOTALL)
        # Remove images
        text = re.sub(r"!\[[^\]]*\]\([^)]*\)", "", text)
        # Strip link URLs but keep text
        text = re.sub(r"\[([^\]]+)\]\([^)]*\)", r"\1", text)
        # Strip Bold/Italic stars
        text = re.sub(r"\*\*([^*]+)\*\*", r"\1", text)
        text = re.sub(r"\*([^*]+)\*", r"\1", text)
        # Rough table cleanup (remove separator rows)
        text = re.sub(r"^\|[\s:|-]+\|$", "", text, flags=re.MULTILINE)
        return text.strip()

    # ------------------------------------------------------------------
    # QR Code Login (未更改，保持原样)
    # ------------------------------------------------------------------
    async def _qr_login(self) -> bool:
        try:
            logger.info("Starting WeChat QR code login...")
            data = await self._api_get("ilink/bot/get_bot_qrcode", params={"bot_type": "3"}, auth=False)
            qrcode_img_content = data.get("qrcode_img_content", "")
            qrcode_id = data.get("qrcode", "")

            if not qrcode_id:
                logger.error("Failed to get QR code from WeChat API: {}", data)
                return False

            scan_url = qrcode_img_content or qrcode_id
            self._print_qr_code(scan_url)
            logger.info("Waiting for QR code scan...")
            
            while self._running:
                try:
                    status_data = await self._api_get(
                        "ilink/bot/get_qrcode_status",
                        params={"qrcode": qrcode_id}, auth=False,
                        extra_headers={"iLink-App-ClientVersion": "1"}
                    )
                except httpx.TimeoutException:
                    continue

                status = status_data.get("status", "")
                if status == "confirmed":
                    token = status_data.get("bot_token", "")
                    if token:
                        self._token = token
                        if status_data.get("baseurl"):
                            self.config.base_url = status_data.get("baseurl")
                        self._save_state()
                        logger.info("WeChat login successful!")
                        return True
                    return False
                elif status == "scaned":
                    logger.info("QR code scanned, waiting for confirmation...")
                elif status == "expired":
                    logger.warning("QR code expired")
                    return False
                await asyncio.sleep(1)
        except Exception as e:
            logger.error("WeChat QR login failed: {}", e)
        return False

    @staticmethod
    def _print_qr_code(url: str) -> None:
        try:
            import qrcode as qr_lib
            qr = qr_lib.QRCode(border=1)
            qr.add_data(url)
            qr.make(fit=True)
            qr.print_ascii(invert=True)
        except ImportError:
            logger.info("QR code URL: {}", url)

    # ------------------------------------------------------------------
    # Channel lifecycle
    # ------------------------------------------------------------------
    async def login(self, force: bool = False) -> bool:
        if force:
            self._token = ""
            self._get_updates_buf = ""
            state_file = self._get_state_dir() / "account.json"
            if state_file.exists():
                state_file.unlink()
        if self._token or self._load_state():
            return True

        self._client = httpx.AsyncClient(timeout=httpx.Timeout(60, connect=30), follow_redirects=True)
        self._running = True
        try:
            return await self._qr_login()
        finally:
            self._running = False
            if self._client:
                await self._client.aclose()
                self._client = None

    async def start(self) -> None:
        self._running = True
        self._next_poll_timeout_s = self.config.poll_timeout
        self._client = httpx.AsyncClient(timeout=httpx.Timeout(self._next_poll_timeout_s + 10, connect=30), follow_redirects=True)

        if self.config.token:
            self._token = self.config.token
        elif not self._load_state():
            if not await self._qr_login():
                logger.error("WeChat login failed.")
                self._running = False
                return

        logger.info("WeChat channel starting with long-poll...")
        consecutive_failures = 0
        while self._running:
            try:
                await self._poll_once()
                consecutive_failures = 0
            except httpx.TimeoutException:
                continue
            except Exception as e:
                if not self._running: break
                consecutive_failures += 1
                logger.error("WeChat poll error ({}/{}): {}", consecutive_failures, MAX_CONSECUTIVE_FAILURES, e)
                if consecutive_failures >= MAX_CONSECUTIVE_FAILURES:
                    consecutive_failures = 0
                    await asyncio.sleep(BACKOFF_DELAY_S)
                else:
                    await asyncio.sleep(RETRY_DELAY_S)

    async def stop(self) -> None:
        self._running = False
        if self._poll_task and not self._poll_task.done():
            self._poll_task.cancel()
        if self._client:
            await self._client.aclose()
            self._client = None
        self._save_state()
        logger.info("WeChat channel stopped")

    # ------------------------------------------------------------------
    # Polling  (增强：全局 Session Guard 熔断支持)
    # ------------------------------------------------------------------
    async def _poll_once(self) -> None:
        body: dict[str, Any] = {"get_updates_buf": self._get_updates_buf, "base_info": BASE_INFO}
        assert self._client is not None
        self._client.timeout = httpx.Timeout(self._next_poll_timeout_s + 10, connect=30)

        data = await self._api_post("ilink/bot/getupdates", body)

        ret = data.get("ret", 0)
        errcode = data.get("errcode", 0)
        is_error = (ret is not None and ret != 0) or (errcode is not None and errcode != 0)

        if is_error:
            if errcode == ERRCODE_SESSION_EXPIRED or ret == ERRCODE_SESSION_EXPIRED:
                logger.warning("WeChat session expired (errcode {}). Pausing 60 min.", errcode)
                self._session_paused_until = time.time() + 3600  # 写入熔断时间戳
                self._save_state()
                await asyncio.sleep(3600)
                return
            raise RuntimeError(f"getUpdates failed: ret={ret} errcode={errcode} errmsg={data.get('errmsg', '')}")

        server_timeout_ms = data.get("longpolling_timeout_ms")
        if server_timeout_ms and server_timeout_ms > 0:
            self._next_poll_timeout_s = max(server_timeout_ms // 1000, 5)

        new_buf = data.get("get_updates_buf", "")
        if new_buf:
            self._get_updates_buf = new_buf
            self._save_state()

        msgs: list[dict] = data.get("msgs", []) or []
        for msg in msgs:
            try:
                await self._process_message(msg)
            except Exception as e:
                logger.error("Error processing WeChat message: {}", e)

    # ------------------------------------------------------------------
    # Inbound message processing
    # ------------------------------------------------------------------
    async def _process_message(self, msg: dict) -> None:
        if msg.get("message_type") == MESSAGE_TYPE_BOT: return

        msg_id = str(msg.get("message_id", "") or msg.get("seq", ""))
        if not msg_id: msg_id = f"{msg.get('from_user_id', '')}_{msg.get('create_time_ms', '')}"
        
        if msg_id in self._processed_ids: return
        self._processed_ids[msg_id] = None
        while len(self._processed_ids) > 1000: self._processed_ids.popitem(last=False)

        from_user_id = msg.get("from_user_id", "") or ""
        if not from_user_id: return

        ctx_token = msg.get("context_token", "")
        if ctx_token:
            self._context_tokens[from_user_id] = ctx_token
            self._save_state() # 保存 Token 防止宕机丢失

        item_list: list[dict] = msg.get("item_list") or []
        content_parts, media_paths = [], []

        for item in item_list:
            item_type = item.get("type", 0)
            if item_type == ITEM_TEXT:
                text = (item.get("text_item") or {}).get("text", "")
                if text:
                    ref = item.get("ref_msg")
                    if ref:
                        ref_item = ref.get("message_item")
                        if ref_item and ref_item.get("type", 0) in (ITEM_IMAGE, ITEM_VOICE, ITEM_FILE, ITEM_VIDEO):
                            content_parts.append(text)
                        else:
                            parts: list[str] = []
                            if ref.get("title"): parts.append(ref["title"])
                            if ref_item:
                                ref_text = (ref_item.get("text_item") or {}).get("text", "")
                                if ref_text: parts.append(ref_text)
                            content_parts.append(f"[引用: {' | '.join(parts)}]\n{text}" if parts else text)
                    else:
                        content_parts.append(text)
            elif item_type == ITEM_IMAGE:
                file_path = await self._download_media_item(item.get("image_item") or {}, "image")
                if file_path:
                    content_parts.append(f"[image]\n[Image: source: {file_path}]")
                    media_paths.append(file_path)
            elif item_type == ITEM_VOICE:
                voice_item = item.get("voice_item") or {}
                voice_text = voice_item.get("text", "")
                if voice_text:
                    content_parts.append(f"[voice] {voice_text}")
                else:
                    file_path = await self._download_media_item(voice_item, "voice")
                    if file_path:
                        silk_path = Path(file_path)
                        silk_data = silk_path.read_bytes()

                        # 尝试将 SILK 转码为 WAV
                        wav_data = silk_to_wav(silk_data)

                        if wav_data:
                            # 转码成功，保存为 .wav 并删除原 .silk 文件
                            wav_path = silk_path.with_suffix(".wav")
                            wav_path.write_bytes(wav_data)
                            silk_path.unlink(missing_ok=True)
                            final_path = str(wav_path)
                            logger.debug(f"SILK transcoded to WAV: {final_path}")
                        else:
                            # 转码失败，使用原始 .silk 文件
                            final_path = file_path

                        # 尝试语音识别
                        transcription = await self.transcribe_audio(final_path)
                        if transcription:
                            content_parts.append(f"[voice] {transcription}")
                        else:
                            content_parts.append(f"[voice]\n[Audio: source: {final_path}]")
                        media_paths.append(final_path)
            elif item_type == ITEM_FILE:
                file_item = item.get("file_item") or {}
                file_name = file_item.get("file_name", "unknown")
                file_path = await self._download_media_item(file_item, "file", file_name)
                if file_path:
                    content_parts.append(f"[file: {file_name}]\n[File: source: {file_path}]")
                    media_paths.append(file_path)
            elif item_type == ITEM_VIDEO:
                file_path = await self._download_media_item(item.get("video_item") or {}, "video")
                if file_path:
                    content_parts.append(f"[video]\n[Video: source: {file_path}]")
                    media_paths.append(file_path)

        content = "\n".join(content_parts)
        if not content: return

        await self._handle_message(
            sender_id=from_user_id, chat_id=from_user_id,
            content=content, media=media_paths or None,
            metadata={"message_id": msg_id},
        )

    # ------------------------------------------------------------------
    # Media download
    # ------------------------------------------------------------------
    async def _download_media_item(self, typed_item: dict, media_type: str, filename: str | None = None) -> str | None:
        try:
            media = typed_item.get("media") or {}
            encrypt_query_param = media.get("encrypt_query_param", "")
            if not encrypt_query_param: return None

            raw_aeskey_hex = typed_item.get("aeskey", "")
            media_aes_key_b64 = media.get("aes_key", "")
            aes_key_b64: str = ""
            
            if raw_aeskey_hex:
                aes_key_b64 = base64.b64encode(bytes.fromhex(raw_aeskey_hex)).decode()
            elif media_aes_key_b64:
                aes_key_b64 = media_aes_key_b64

            cdn_url = f"{self.config.cdn_base_url}/download?encrypted_query_param={quote(encrypt_query_param)}"
            assert self._client is not None
            resp = await self._client.get(cdn_url)
            resp.raise_for_status()
            data = resp.content

            if aes_key_b64 and data:
                data = _decrypt_aes_ecb(data, aes_key_b64)

            if not data: return None

            media_dir = get_media_dir("weixin")
            ext = _ext_for_type(media_type)
            if not filename:
                ts, h = int(time.time()), abs(hash(encrypt_query_param)) % 100000
                filename = f"{media_type}_{ts}_{h}{ext}"
            file_path = media_dir / os.path.basename(filename)
            file_path.write_bytes(data)
            return str(file_path)
        except Exception as e:
            logger.error("Error downloading WeChat media: {}", e)
            return None

    # ------------------------------------------------------------------
    # Outbound (增强：Session Guard 拦截与 Markdown 清洗)
    # ------------------------------------------------------------------
    async def send(self, msg: OutboundMessage) -> None:
        # 1. 熔断检查 (Session Guard): 防止被踢下线后持续发包被封号
        if time.time() < self._session_paused_until:
            logger.warning("WeChat session is paused until {}. Dropping outbound message.", time.ctime(self._session_paused_until))
            return

        if not self._client or not self._token:
            logger.warning("WeChat client not initialized or not authenticated")
            return

        # 2. Markdown 清洗: 防止微信无法渲染 MD 标签
        content = self._markdown_to_plain_text(msg.content)
        ctx_token = self._context_tokens.get(msg.chat_id, "")
        
        if not ctx_token:
            logger.warning("WeChat: no context_token for chat_id={}, message may not show as reply", msg.chat_id)

        for media_path in (msg.media or []):
            try:
                await self._send_media_file(msg.chat_id, media_path, ctx_token)
            except Exception as e:
                filename = Path(media_path).name
                logger.error("Failed to send WeChat media {}: {}", media_path, e)
                await self._send_text(msg.chat_id, f"[Failed to send: {filename}]", ctx_token)

        if not content: return

        try:
            chunks = split_message(content, WEIXIN_MAX_MESSAGE_LEN)
            for chunk in chunks:
                await self._send_text(msg.chat_id, chunk, ctx_token)
        except Exception as e:
            logger.error("Error sending WeChat message: {}", e)

    async def _send_text(self, to_user_id: str, text: str, context_token: str) -> None:
        client_id = f"nanobot-{uuid.uuid4().hex[:12]}"
        item_list = [{"type": ITEM_TEXT, "text_item": {"text": text}}] if text else []
        
        weixin_msg: dict[str, Any] = {
            "from_user_id": "",
            "to_user_id": to_user_id,
            "client_id": client_id,
            "message_type": MESSAGE_TYPE_BOT,
            "message_state": MESSAGE_STATE_FINISH,
        }
        if item_list: weixin_msg["item_list"] = item_list
        if context_token: weixin_msg["context_token"] = context_token

        body = {"msg": weixin_msg, "base_info": BASE_INFO}
        data = await self._api_post("ilink/bot/sendmessage", body)
        
        errcode = data.get("errcode", 0)
        if errcode != 0:
            logger.warning("WeChat send error (code {}): {}", errcode, data.get("errmsg", ""))

    async def _send_media_file(self, to_user_id: str, media_path: str, context_token: str) -> None:
        p = Path(media_path)
        if not p.is_file(): raise FileNotFoundError(f"Media file not found: {media_path}")

        raw_data, raw_size = p.read_bytes(), p.stat().st_size
        raw_md5 = hashlib.md5(raw_data).hexdigest()

        ext = p.suffix.lower()
        if ext in _IMAGE_EXTS: upload_type, item_type, item_key = UPLOAD_MEDIA_IMAGE, ITEM_IMAGE, "image_item"
        elif ext in _VIDEO_EXTS: upload_type, item_type, item_key = UPLOAD_MEDIA_VIDEO, ITEM_VIDEO, "video_item"
        else: upload_type, item_type, item_key = UPLOAD_MEDIA_FILE, ITEM_FILE, "file_item"

        aes_key_raw = os.urandom(16)
        aes_key_hex = aes_key_raw.hex()
        padded_size = ((raw_size + 1 + 15) // 16) * 16

        # Step 1: Get upload URL
        file_key = os.urandom(16).hex()
        upload_body: dict[str, Any] = {
            "filekey": file_key, "media_type": upload_type, "to_user_id": to_user_id,
            "rawsize": raw_size, "rawfilemd5": raw_md5, "filesize": padded_size,
            "no_need_thumb": True, "aeskey": aes_key_hex,
        }

        assert self._client is not None
        upload_resp = await self._api_post("ilink/bot/getuploadurl", upload_body)
        upload_param = upload_resp.get("upload_param", "")
        if not upload_param: raise RuntimeError(f"getuploadurl returned no upload_param")

        # Step 2: AES-128-ECB encrypt and POST to CDN (增强：3次循环重试防弱网失败)
        aes_key_b64 = base64.b64encode(aes_key_raw).decode()
        encrypted_data = _encrypt_aes_ecb(raw_data, aes_key_b64)
        cdn_upload_url = f"{self.config.cdn_base_url}/upload?encrypted_query_param={quote(upload_param)}&filekey={quote(file_key)}"
        
        download_param = ""
        for attempt in range(1, 4):
            try:
                cdn_resp = await self._client.post(
                    cdn_upload_url, content=encrypted_data, headers={"Content-Type": "application/octet-stream"}
                )
                cdn_resp.raise_for_status()
                download_param = cdn_resp.headers.get("x-encrypted-param", "")
                if download_param:
                    break
                logger.warning(f"WeChat CDN upload attempt {attempt} missing x-encrypted-param header")
            except Exception as e:
                logger.warning(f"WeChat CDN upload attempt {attempt} failed: {e}")
            
            if attempt < 3: await asyncio.sleep(2)

        if not download_param:
            raise RuntimeError("CDN upload failed after 3 attempts or missing x-encrypted-param header")

        # Step 3: Send message
        cdn_aes_key_b64 = base64.b64encode(aes_key_hex.encode()).decode()
        media_item: dict[str, Any] = {
            "media": {"encrypt_query_param": download_param, "aes_key": cdn_aes_key_b64, "encrypt_type": 1}
        }

        if item_type == ITEM_IMAGE: media_item["mid_size"] = padded_size
        elif item_type == ITEM_VIDEO: media_item["video_size"] = padded_size
        elif item_type == ITEM_FILE: media_item["file_name"] = p.name; media_item["len"] = str(raw_size)

        client_id = f"nanobot-{uuid.uuid4().hex[:12]}"
        weixin_msg: dict[str, Any] = {
            "from_user_id": "", "to_user_id": to_user_id, "client_id": client_id,
            "message_type": MESSAGE_TYPE_BOT, "message_state": MESSAGE_STATE_FINISH,
            "item_list": [{"type": item_type, item_key: media_item}],
            "context_token": context_token
        }

        data = await self._api_post("ilink/bot/sendmessage", {"msg": weixin_msg, "base_info": BASE_INFO})
        if data.get("errcode", 0) != 0:
            raise RuntimeError(f"WeChat send media error: {data.get('errmsg', '')}")
        logger.info("WeChat media sent: {}", p.name)

# ---------------------------------------------------------------------------
# AES-128-ECB encryption / decryption
# ---------------------------------------------------------------------------
def _parse_aes_key(aes_key_b64: str) -> bytes:
    decoded = base64.b64decode(aes_key_b64)
    if len(decoded) == 16: return decoded
    if len(decoded) == 32 and re.fullmatch(rb"[0-9a-fA-F]{32}", decoded):
        return bytes.fromhex(decoded.decode("ascii"))
    raise ValueError(f"aes_key decode error, got {len(decoded)} bytes")

def _encrypt_aes_ecb(data: bytes, aes_key_b64: str) -> bytes:
    try: key = _parse_aes_key(aes_key_b64)
    except Exception: return data
    pad_len = 16 - len(data) % 16
    padded = data + bytes([pad_len] * pad_len)
    try:
        from Crypto.Cipher import AES
        return AES.new(key, AES.MODE_ECB).encrypt(padded)
    except ImportError: pass
    try:
        from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
        encryptor = Cipher(algorithms.AES(key), modes.ECB()).encryptor()
        return encryptor.update(padded) + encryptor.finalize()
    except ImportError: return data

def _decrypt_aes_ecb(data: bytes, aes_key_b64: str) -> bytes:
    try: key = _parse_aes_key(aes_key_b64)
    except Exception: return data
    try:
        from Crypto.Cipher import AES
        return AES.new(key, AES.MODE_ECB).decrypt(data)
    except ImportError: pass
    try:
        from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
        decryptor = Cipher(algorithms.AES(key), modes.ECB()).decryptor()
        return decryptor.update(data) + decryptor.finalize()
    except ImportError: return data

def _ext_for_type(media_type: str) -> str:
    return {"image": ".jpg", "voice": ".silk", "video": ".mp4", "file": ""}.get(media_type, "")

def silk_to_wav(silk_data: bytes, sample_rate: int = 24000) -> bytes | None:
    """
    将微信的 SILK 语音流在内存中无缝转换为标准 WAV (16-bit PCM) 格式。
    依赖包: pip install silk-python
    """
    try:
        from pysilk import decode
    except ImportError:
        logger.warning("Missing 'silk-python' library. Cannot transcode SILK. Run: pip install silk-python")
        return None

    try:
        # 微信 SILK 文件通常以 "#!SILK_V3" 开头，需要去掉这个 9 字节的头部
        if silk_data.startswith(b"#!SILK_V3"):
            silk_data = silk_data[9:]

        logger.debug(f"Decoding {len(silk_data)} bytes of SILK data...")

        # 使用 pysilk 将 SILK 解码为原始的 PCM 字节流
        silk_io = io.BytesIO(silk_data)
        pcm_io = io.BytesIO()
        decode(silk_io, pcm_io, sample_rate)
        pcm_data = pcm_io.getvalue()
        logger.debug(f"Decoded to {len(pcm_data)} bytes of PCM data.")

        # 使用 Python 内置的 wave 库，将 PCM 包装成标准 WAV 容器
        wav_io = io.BytesIO()
        with wave.open(wav_io, 'wb') as wav_file:
            wav_file.setnchannels(1)           # 单声道 (Mono)
            wav_file.setsampwidth(2)           # 16-bit 采样深度
            wav_file.setframerate(sample_rate)  # 采样率 (微信默认 24000)
            wav_file.writeframes(pcm_data)

        wav_bytes = wav_io.getvalue()
        logger.debug(f"Successfully generated WAV data (size: {len(wav_bytes)})")
        return wav_bytes

    except Exception as e:
        logger.error(f"SILK transcode failed: {e}")
        return None