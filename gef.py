#######################################################################################
# GEF - Multi-Architecture GDB Enhanced Features for Exploiters & Reverse-Engineers
#
# by  @_hugsy_
#######################################################################################
#
# GEF is a kick-ass set of commands for X86, ARM, MIPS, PowerPC and SPARC to
# make GDB cool again for exploit dev. It is aimed to be used mostly by exploit
# devs and reversers, to provides additional features to GDB using the Python
# API to assist during the process of dynamic analysis.
#
# GEF fully relies on GDB API and other Linux-specific sources of information
# (such as /proc/<pid>). As a consequence, some of the features might not work
# on custom or hardened systems such as GrSec.
#
# Since January 2020, GEF solely support GDB compiled with Python3 and was tested on
#   * x86-32 & x86-64
#   * arm v5,v6,v7
#   * aarch64 (armv8)
#   * mips & mips64
#   * powerpc & powerpc64
#   * sparc & sparc64(v9)
#
# For GEF with Python2 (only) support was moved to the GEF-Legacy
# (https://github.com/hugsy/gef-legacy)
#
# To start: in gdb, type `source /path/to/gef.py`
#
#######################################################################################
#
# gef is distributed under the MIT License (MIT)
# Copyright (c) 2013-2022 crazy rabbidz
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

import abc
import argparse
import ast
import binascii
import codecs
import collections
import configparser
import ctypes
import enum
import functools
import hashlib
import importlib
import inspect
import itertools
import json
import os
import pathlib
import platform
import re
import shutil
import site
import socket
import string
import struct
import subprocess
import sys
import tempfile
import time
import traceback
import warnings
from functools import lru_cache
from io import StringIO, TextIOWrapper
from types import ModuleType
from typing import (Any, ByteString, Callable, Dict, Generator, Iterable,
                    Iterator, List, NoReturn, Optional, Sequence, Set, Tuple, Type,
                    Union)
from urllib.request import urlopen


def http_get(url: str) -> Optional[bytes]:
    """Basic HTTP wrapper for GET request. Return the body of the page if HTTP code is OK,
    otherwise return None."""
    try:
        http = urlopen(url)
        return http.read() if http.getcode() == 200 else None
    except Exception:
        return None


def update_gef(argv: List[str]) -> int:
    """Try to update `gef` to the latest version pushed on GitHub main branch.
    Return 0 on success, 1 on failure. """
    ver = "dev" if "--dev" in argv else GEF_DEFAULT_BRANCH
    latest_gef_data = http_get(f"https://raw.githubusercontent.com/hugsy/gef/{ver}/scripts/gef.sh")
    if not latest_gef_data:
        print("[-] Failed to get remote gef")
        return 1
    with tempfile.NamedTemporaryFile(suffix=".sh") as fd:
        fd.write(latest_gef_data)
        fd.flush()
        fpath = pathlib.Path(fd.name)
        return subprocess.run(["bash", fpath, ver], stdout=subprocess.DEVNULL,
                              stderr=subprocess.DEVNULL).returncode


try:
    import gdb  # type:ignore
except ImportError:
    # if out of gdb, the only action allowed is to update gef.py
    if len(sys.argv) >= 2 and sys.argv[1].lower() in ("--update", "--upgrade"):
        sys.exit(update_gef(sys.argv[2:]))
    print("[-] gef cannot run as standalone")
    sys.exit(0)


GDB_MIN_VERSION                        = (8, 0)
GDB_VERSION                            = tuple(map(int, re.search(r"(\d+)[^\d]+(\d+)", gdb.VERSION).groups()))
PYTHON_MIN_VERSION                     = (3, 6)
PYTHON_VERSION                         = sys.version_info[0:2]

DEFAULT_PAGE_ALIGN_SHIFT               = 12
DEFAULT_PAGE_SIZE                      = 1 << DEFAULT_PAGE_ALIGN_SHIFT

GEF_RC                                 = (pathlib.Path(os.getenv("GEF_RC", "")).absolute()
                                          if os.getenv("GEF_RC")
                                          else pathlib.Path().home() / ".gef.rc")
GEF_TEMP_DIR                           = os.path.join(tempfile.gettempdir(), "gef")
GEF_MAX_STRING_LENGTH                  = 50

ANSI_SPLIT_RE                          = r"(\033\[[\d;]*m)"

LEFT_ARROW                             = " ← "
RIGHT_ARROW                            = " → "
DOWN_ARROW                             = "↳"
HORIZONTAL_LINE                        = "─"
VERTICAL_LINE                          = "│"
CROSS                                  = "✘ "
TICK                                   = "✓ "
BP_GLYPH                               = "●"
GEF_PROMPT                             = "gef➤  "
GEF_PROMPT_ON                          = f"\001\033[1;32m\002{GEF_PROMPT}\001\033[0m\002"
GEF_PROMPT_OFF                         = f"\001\033[1;31m\002{GEF_PROMPT}\001\033[0m\002"

GEF_DEFAULT_BRANCH                     = "main"
GEF_EXTRAS_DEFAULT_BRANCH              = "main"

gef : "Gef"
__registered_commands__ : Set[Type["GenericCommand"]]                                        = set()
__registered_functions__ : Set[Type["GenericFunction"]]                                      = set()
__registered_architectures__ : Dict[Union["Elf.Abi", str], Type["Architecture"]]              = {}
__registered_file_formats__ : Set[ Type["FileFormat"] ]                                       = set()


def reset_all_caches() -> None:
    """Free all caches. If an object is cached, it will have a callable attribute `cache_clear`
    which will be invoked to purge the function cache."""

    for mod in dir(sys.modules["__main__"]):
        obj = getattr(sys.modules["__main__"], mod)
        if hasattr(obj, "cache_clear"):
            obj.cache_clear()

    gef.reset_caches()
    return


def reset() -> None:
    global gef

    if "gef" in locals().keys():
        reset_all_caches()
        del gef

    gef = Gef()
    gef.setup()

    gef.arch = ARM()


def highlight_text(text: str) -> str:
    """
    Highlight text using `gef.ui.highlight_table` { match -> color } settings.

    If RegEx is enabled it will create a match group around all items in the
    `gef.ui.highlight_table` and wrap the specified color in the `gef.ui.highlight_table`
    around those matches.

    If RegEx is disabled, split by ANSI codes and 'colorify' each match found
    within the specified string.
    """
    global gef

    if not gef.ui.highlight_table:
        return text

    if gef.config["highlight.regex"]:
        for match, color in gef.ui.highlight_table.items():
            text = re.sub("(" + match + ")", Color.colorify("\\1", color), text)
        return text

    ansiSplit = re.split(ANSI_SPLIT_RE, text)

    for match, color in gef.ui.highlight_table.items():
        for index, val in enumerate(ansiSplit):
            found = val.find(match)
            if found > -1:
                ansiSplit[index] = val.replace(match, Color.colorify(match, color))
                break
        text = "".join(ansiSplit)
        ansiSplit = re.split(ANSI_SPLIT_RE, text)

    return "".join(ansiSplit)


def gef_print(*args: str, end="\n", sep=" ", **kwargs: Any) -> None:
    """Wrapper around print(), using string buffering feature."""
    parts = [highlight_text(a) for a in args]
    if gef.ui.stream_buffer and not is_debug():
        gef.ui.stream_buffer.write(sep.join(parts) + end)
        return

    print(*parts, sep=sep, end=end, **kwargs)
    return


def bufferize(f: Callable) -> Callable:
    """Store the content to be printed for a function in memory, and flush it on function exit."""

    @functools.wraps(f)
    def wrapper(*args: Any, **kwargs: Any) -> Any:
        global gef

        if gef.ui.stream_buffer:
            return f(*args, **kwargs)

        gef.ui.stream_buffer = StringIO()
        try:
            rv = f(*args, **kwargs)
        finally:
            redirect = gef.config["context.redirect"]
            if redirect.startswith("/dev/pts/"):
                if not gef.ui.redirect_fd:
                    # if the FD has never been open, open it
                    fd = open(redirect, "wt")
                    gef.ui.redirect_fd = fd
                elif redirect != gef.ui.redirect_fd.name:
                    # if the user has changed the redirect setting during runtime, update the state
                    gef.ui.redirect_fd.close()
                    fd = open(redirect, "wt")
                    gef.ui.redirect_fd = fd
                else:
                    # otherwise, keep using it
                    fd = gef.ui.redirect_fd
            else:
                fd = sys.stdout
                gef.ui.redirect_fd = None

            if gef.ui.redirect_fd and fd.closed:
                # if the tty was closed, revert back to stdout
                fd = sys.stdout
                gef.ui.redirect_fd = None
                gef.config["context.redirect"] = ""

            fd.write(gef.ui.stream_buffer.getvalue())
            fd.flush()
            gef.ui.stream_buffer = None
        return rv

    return wrapper


#
# Helpers
#

def p8(x: int, s: bool = False, e: Optional["Endianness"] = None) -> bytes:
    """Pack one byte respecting the current architecture endianness."""
    endian = e or gef.arch.endianness
    return struct.pack(f"{endian}B", x) if not s else struct.pack(f"{endian:s}b", x)


def p16(x: int, s: bool = False, e: Optional["Endianness"] = None) -> bytes:
    """Pack one word respecting the current architecture endianness."""
    endian = e or gef.arch.endianness
    return struct.pack(f"{endian}H", x) if not s else struct.pack(f"{endian:s}h", x)


def p32(x: int, s: bool = False, e: Optional["Endianness"] = None) -> bytes:
    """Pack one dword respecting the current architecture endianness."""
    endian = e or gef.arch.endianness
    return struct.pack(f"{endian}I", x) if not s else struct.pack(f"{endian:s}i", x)


def p64(x: int, s: bool = False, e: Optional["Endianness"] = None) -> bytes:
    """Pack one qword respecting the current architecture endianness."""
    endian = e or gef.arch.endianness
    return struct.pack(f"{endian}Q", x) if not s else struct.pack(f"{endian:s}q", x)


def u8(x: bytes, s: bool = False, e: Optional["Endianness"] = None) -> int:
    """Unpack one byte respecting the current architecture endianness."""
    endian = e or gef.arch.endianness
    return struct.unpack(f"{endian}B", x)[0] if not s else struct.unpack(f"{endian:s}b", x)[0]


def u16(x: bytes, s: bool = False, e: Optional["Endianness"] = None) -> int:
    """Unpack one word respecting the current architecture endianness."""
    endian = e or gef.arch.endianness
    return struct.unpack(f"{endian}H", x)[0] if not s else struct.unpack(f"{endian:s}h", x)[0]


def u32(x: bytes, s: bool = False, e: Optional["Endianness"] = None) -> int:
    """Unpack one dword respecting the current architecture endianness."""
    endian = e or gef.arch.endianness
    return struct.unpack(f"{endian}I", x)[0] if not s else struct.unpack(f"{endian:s}i", x)[0]


def u64(x: bytes, s: bool = False, e: Optional["Endianness"] = None) -> int:
    """Unpack one qword respecting the current architecture endianness."""
    endian = e or gef.arch.endianness
    return struct.unpack(f"{endian}Q", x)[0] if not s else struct.unpack(f"{endian:s}q", x)[0]


def is_ascii_string(address: int) -> bool:
    """Helper function to determine if the buffer pointed by `address` is an ASCII string (in GDB)"""
    try:
        return gef.memory.read_ascii_string(address) is not None
    except Exception:
        return False


def is_alive() -> bool:
    """Check if GDB is running."""
    try:
        return gdb.selected_inferior().pid > 0
    except Exception:
        return False


#
# Decorators
#
def only_if_gdb_running(f: Callable) -> Callable:
    """Decorator wrapper to check if GDB is running."""

    @functools.wraps(f)
    def wrapper(*args: Any, **kwargs: Any) -> Any:
        if is_alive():
            return f(*args, **kwargs)
        else:
            warn("No debugging session active")

    return wrapper


def only_if_gdb_target_local(f: Callable) -> Callable:
    """Decorator wrapper to check if GDB is running locally (target not remote)."""

    @functools.wraps(f)
    def wrapper(*args: Any, **kwargs: Any) -> Any:
        if not is_remote_debug():
            return f(*args, **kwargs)
        else:
            warn("This command cannot work for remote sessions.")

    return wrapper


def deprecated(solution: str = "") -> Callable:
    """Decorator to add a warning when a command is obsolete and will be removed."""
    def decorator(f: Callable) -> Callable:
        @functools.wraps(f)
        def wrapper(*args: Any, **kwargs: Any) -> Any:
            caller = inspect.stack()[1]
            caller_file = pathlib.Path(caller.filename)
            caller_loc = caller.lineno
            msg = f"{caller_file.name}:L{caller_loc} '{f.__name__}' is deprecated and will be removed in a feature release. "
            if not gef:
                print(msg)
            elif gef.config["gef.show_deprecation_warnings"] is True:
                if solution:
                    msg += solution
                warn(msg)
            return f(*args, **kwargs)

        if not wrapper.__doc__:
            wrapper.__doc__ = ""
        wrapper.__doc__ += f"\r\n`{f.__name__}` is **DEPRECATED** and will be removed in the future.\r\n{solution}"
        return wrapper
    return decorator


def experimental_feature(f: Callable) -> Callable:
    """Decorator to add a warning when a feature is experimental."""

    @functools.wraps(f)
    def wrapper(*args: Any, **kwargs: Any) -> Any:
        warn("This feature is under development, expect bugs and unstability...")
        return f(*args, **kwargs)

    return wrapper


def only_if_events_supported(event_type: str) -> Callable:
    """Checks if GDB supports events without crashing."""
    def wrap(f: Callable) -> Callable:
        def wrapped_f(*args: Any, **kwargs: Any) -> Any:
            if getattr(gdb, "events") and getattr(gdb.events, event_type):
                return f(*args, **kwargs)
            warn("GDB events cannot be set")
        return wrapped_f
    return wrap


class classproperty(property):
    """Make the attribute a `classproperty`."""
    def __get__(self, cls, owner):
        return classmethod(self.fget).__get__(None, owner)()


def FakeExit(*args: Any, **kwargs: Any) -> NoReturn:
    raise RuntimeWarning


sys.exit = FakeExit


def parse_arguments(required_arguments: Dict[Union[str, Tuple[str, str]], Any],
                    optional_arguments: Dict[Union[str, Tuple[str, str]], Any]) -> Callable:
    """Argument parsing decorator."""

    def int_wrapper(x: str) -> int: return int(x, 0)

    def decorator(f: Callable) -> Optional[Callable]:
        def wrapper(*args: Any, **kwargs: Any) -> Callable:
            parser = argparse.ArgumentParser(prog=args[0]._cmdline_, add_help=True)
            for argname in required_arguments:
                argvalue = required_arguments[argname]
                argtype = type(argvalue)
                if argtype is int:
                    argtype = int_wrapper

                argname_is_list = not isinstance(argname, str)
                assert not argname_is_list and isinstance(argname, str)
                if not argname_is_list and argname.startswith("-"):
                    # optional args
                    if argtype is bool:
                        parser.add_argument(argname, action="store_true" if argvalue else "store_false")
                    else:
                        parser.add_argument(argname, type=argtype, required=True, default=argvalue)
                else:
                    if argtype in (list, tuple):
                        nargs = "*"
                        argtype = type(argvalue[0])
                    else:
                        nargs = "?"
                    # positional args
                    parser.add_argument(argname, type=argtype, default=argvalue, nargs=nargs)

            for argname in optional_arguments:
                if isinstance(argname, str) and not argname.startswith("-"):
                    # refuse positional arguments
                    continue
                argvalue = optional_arguments[argname]
                argtype = type(argvalue)
                if isinstance(argname, str):
                    argname = [argname,]
                if argtype is int:
                    argtype = int_wrapper
                if argtype is bool:
                    parser.add_argument(*argname, action="store_true" if argvalue else "store_false")
                else:
                    parser.add_argument(*argname, type=argtype, default=argvalue)

            parsed_args = parser.parse_args(*(args[1:]))
            kwargs["arguments"] = parsed_args
            return f(*args, **kwargs)
        return wrapper
    return decorator


class Color:
    """Used to colorify terminal output."""
    colors = {
        "normal"         : "\033[0m",
        "gray"           : "\033[2m",
        "light_gray"     : "\033[0;37m",
        "red"            : "\033[31m",
        "green"          : "\033[32m",
        "yellow"         : "\033[33m",
        "blue"           : "\033[34m",
        "pink"           : "\033[35m",
        "cyan"           : "\033[36m",
        "bold"           : "\033[1m",
        "underline"      : "\033[4m",
        "underline_off"  : "\033[24m",
        "highlight"      : "\033[3m",
        "highlight_off"  : "\033[23m",
        "blink"          : "\033[5m",
        "blink_off"      : "\033[25m",
    }

    @staticmethod
    def redify(msg: str) -> str:        return Color.colorify(msg, "red")
    @staticmethod
    def greenify(msg: str) -> str:      return Color.colorify(msg, "green")
    @staticmethod
    def blueify(msg: str) -> str:       return Color.colorify(msg, "blue")
    @staticmethod
    def yellowify(msg: str) -> str:     return Color.colorify(msg, "yellow")
    @staticmethod
    def grayify(msg: str) -> str:       return Color.colorify(msg, "gray")
    @staticmethod
    def light_grayify(msg: str) -> str: return Color.colorify(msg, "light_gray")
    @staticmethod
    def pinkify(msg: str) -> str:       return Color.colorify(msg, "pink")
    @staticmethod
    def cyanify(msg: str) -> str:       return Color.colorify(msg, "cyan")
    @staticmethod
    def boldify(msg: str) -> str:       return Color.colorify(msg, "bold")
    @staticmethod
    def underlinify(msg: str) -> str:   return Color.colorify(msg, "underline")
    @staticmethod
    def highlightify(msg: str) -> str:  return Color.colorify(msg, "highlight")
    @staticmethod
    def blinkify(msg: str) -> str:      return Color.colorify(msg, "blink")

    @staticmethod
    def colorify(text: str, attrs: str) -> str:
        """Color text according to the given attributes."""
        if gef.config["gef.disable_color"] is True: return text

        colors = Color.colors
        msg = [colors[attr] for attr in attrs.split() if attr in colors]
        msg.append(str(text))
        if colors["highlight"] in msg:   msg.append(colors["highlight_off"])
        if colors["underline"] in msg:   msg.append(colors["underline_off"])
        if colors["blink"] in msg:       msg.append(colors["blink_off"])
        msg.append(colors["normal"])
        return "".join(msg)


class Address:
    """GEF representation of memory addresses."""
    def __init__(self, **kwargs: Any) -> None:
        self.value: int = kwargs.get("value", 0)
        self.section: "Section" = kwargs.get("section", None)
        self.info: "Zone" = kwargs.get("info", None)
        return

    def __str__(self) -> str:
        value = format_address(self.value)
        rom0_color = gef.config["theme.address_rom0"]
        iwram_color = gef.config["theme.address_iwram"]
        ewram_color = gef.config["theme.address_ewram"]
        if self.is_in_rom0():
            return Color.colorify(value, rom0_color)
        if self.is_in_ewram():
            return Color.colorify(value, ewram_color)
        if self.is_in_iwram():
            return Color.colorify(value, iwram_color)
        return value

    def __int__(self) -> int:
        return self.value

    def is_in_bios(self) -> bool:
        return hasattr(self.section, "name") and "BIOS" == self.section.name

    def is_in_rom0(self) -> bool:
        return hasattr(self.section, "name") and "ROM0" == self.section.name

    def is_in_iwram(self) -> bool:
        return hasattr(self.section, "name") and "IWRAM" == self.section.name

    def is_in_ewram(self) -> bool:
        return hasattr(self.section, "name") and "EWRAM" == self.section.name

    def dereference(self) -> Optional[int]:
        addr = align_address(int(self.value))
        derefed = dereference(addr)
        return None if derefed is None else int(derefed)

    @property
    def valid(self) -> bool:
        return any(map(lambda x: x.start <= self.value < x.end, gef.memory.maps))


class Permission(enum.Flag):
    """GEF representation of Linux permission."""
    NONE      = 0
    EXECUTE   = 1
    WRITE     = 2
    READ      = 4
    ALL       = 7

    def __str__(self) -> str:
        perm_str = ""
        perm_str += "r" if self & Permission.READ else "-"
        perm_str += "w" if self & Permission.WRITE else "-"
        perm_str += "x" if self & Permission.EXECUTE else "-"
        return perm_str

    @staticmethod
    def from_info_sections(*args: str) -> "Permission":
        perm = Permission(0)
        for arg in args:
            if "READONLY" in arg: perm |= Permission.READ
            if "DATA" in arg: perm |= Permission.WRITE
            if "CODE" in arg: perm |= Permission.EXECUTE
        return perm

    @staticmethod
    def from_process_maps(perm_str: str) -> "Permission":
        perm = Permission(0)
        if perm_str[0] == "r": perm |= Permission.READ
        if perm_str[1] == "w": perm |= Permission.WRITE
        if perm_str[2] == "x": perm |= Permission.EXECUTE
        return perm


class Section:
    """GEF representation of process memory sections."""

    def __init__(self, **kwargs: Any) -> None:
        self.start: int = kwargs.get("start", 0)
        self.end: int = kwargs.get("end", 0)
        self.permission: Permission = kwargs.get("permission", Permission(0))
        self.name: str = kwargs.get("name", "")
        return

    def is_readable(self) -> bool:
        return (self.permission & Permission.READ) != 0

    def is_writable(self) -> bool:
        return (self.permission & Permission.WRITE) != 0

    def is_executable(self) -> bool:
        return (self.permission & Permission.EXECUTE) != 0

    @property
    def size(self) -> int:
        if self.end is None or self.start is None:
            return -1
        return self.end - self.start

    def __str__(self) -> str:
        return (f"Section(start={self.start:#x}, end={self.end:#x}, "
                f"permissions={self.permission!s})")


Zone = collections.namedtuple("Zone", ["name", "zone_start", "zone_end", "filename"])


class Endianness(enum.Enum):
    LITTLE_ENDIAN     = 1
    BIG_ENDIAN        = 2

    def __str__(self) -> str:
        return "<" if self == Endianness.LITTLE_ENDIAN else ">"

    def __repr__(self) -> str:
        return self.name

    def __int__(self) -> int:
        return self.value


class FileFormatSection:
    misc: Any


class FileFormat:
    name: str
    path: pathlib.Path
    entry_point: int
    sections: List[FileFormatSection]

    def __init__(self, path: Union[str, pathlib.Path]) -> None:
        raise NotImplemented

    def __init_subclass__(cls: Type["FileFormat"], **kwargs):
        global __registered_file_formats__
        super().__init_subclass__(**kwargs)
        required_attributes = ("name", "entry_point", "is_valid",)
        for attr in required_attributes:
            if not hasattr(cls, attr):
                raise NotImplementedError(f"File format '{cls.__name__}' is invalid: missing attribute '{attr}'")
        __registered_file_formats__.add(cls)
        return

    @classmethod
    def is_valid(cls, path: pathlib.Path) -> bool:
        raise NotImplemented

    def __str__(self) -> str:
        return f"{self.name}('{self.path.absolute()}', entry @ {self.entry_point:#x})"


class Elf(FileFormat):
    """Basic ELF parsing.
    Ref:
    - http://www.skyfree.org/linux/references/ELF_Format.pdf
    - https://refspecs.linuxfoundation.org/elf/elfspec_ppc.pdf
    - https://refspecs.linuxfoundation.org/ELF/ppc64/PPC-elf64abi.html
    """
    class Class(enum.Enum):
        ELF_32_BITS       = 0x01
        ELF_64_BITS       = 0x02

    ELF_MAGIC         = 0x7f454c46

    class Abi(enum.Enum):
        X86_64            = 0x3e
        X86_32            = 0x03
        ARM               = 0x28
        MIPS              = 0x08
        POWERPC           = 0x14
        POWERPC64         = 0x15
        SPARC             = 0x02
        SPARC64           = 0x2b
        AARCH64           = 0xb7
        RISCV             = 0xf3
        IA64              = 0x32
        M68K              = 0x04

    class Type(enum.Enum):
        ET_RELOC          = 1
        ET_EXEC           = 2
        ET_DYN            = 3
        ET_CORE           = 4

    class OsAbi(enum.Enum):
        SYSTEMV     = 0x00
        HPUX        = 0x01
        NETBSD      = 0x02
        LINUX       = 0x03
        SOLARIS     = 0x06
        AIX         = 0x07
        IRIX        = 0x08
        FREEBSD     = 0x09
        OPENBSD     = 0x0C

    e_magic: int                = ELF_MAGIC
    e_class: "Elf.Class"        = Class.ELF_32_BITS
    e_endianness: Endianness    = Endianness.LITTLE_ENDIAN
    e_eiversion: int
    e_osabi: "Elf.OsAbi"
    e_abiversion: int
    e_pad: bytes
    e_type: "Elf.Type"          = Type.ET_EXEC
    e_machine: Abi              = Abi.X86_32
    e_version: int
    e_entry: int
    e_phoff: int
    e_shoff: int
    e_flags: int
    e_ehsize: int
    e_phentsize: int
    e_phnum: int
    e_shentsize: int
    e_shnum: int
    e_shstrndx: int

    path: pathlib.Path
    phdrs : List["Phdr"]
    shdrs : List["Shdr"]
    name: str = "ELF"

    def __init__(self, path: Union[str, pathlib.Path]) -> None:
        """Instantiate an ELF object. A valid ELF must be provided, or an exception will be thrown."""

        if isinstance(path, str):
            self.path = pathlib.Path(path).expanduser()
        elif isinstance(path, pathlib.Path):
            self.path = path
        else:
            raise TypeError

        if not self.path.exists():
            raise FileNotFoundError(f"'{self.path}' not found/readable, most gef features will not work")

        with self.path.open("rb") as self.fd:
            # off 0x0
            self.e_magic, e_class, e_endianness, self.e_eiversion = self.read_and_unpack(">IBBB")
            if self.e_magic != Elf.ELF_MAGIC:
                # The ELF is corrupted, GDB won't handle it, no point going further
                raise RuntimeError("Not a valid ELF file (magic)")

            self.e_class, self.e_endianness = Elf.Class(e_class), Endianness(e_endianness)

            if self.e_endianness != gef.arch.endianness:
                warn("Unexpected endianness for architecture")

            endian = self.e_endianness

            # off 0x7
            e_osabi, self.e_abiversion = self.read_and_unpack(f"{endian}BB")
            self.e_osabi = Elf.OsAbi(e_osabi)

            # off 0x9
            self.e_pad = self.read(7)

            # off 0x10
            e_type, e_machine, self.e_version = self.read_and_unpack(f"{endian}HHI")
            self.e_type, self.e_machine = Elf.Type(e_type), Elf.Abi(e_machine)

            # off 0x18
            if self.e_class == Elf.Class.ELF_64_BITS:
                self.e_entry, self.e_phoff, self.e_shoff = self.read_and_unpack(f"{endian}QQQ")
            else:
                self.e_entry, self.e_phoff, self.e_shoff = self.read_and_unpack(f"{endian}III")

            self.e_flags, self.e_ehsize, self.e_phentsize, self.e_phnum = self.read_and_unpack(f"{endian}IHHH")
            self.e_shentsize, self.e_shnum, self.e_shstrndx = self.read_and_unpack(f"{endian}HHH")

            self.phdrs = []
            for i in range(self.e_phnum):
                self.phdrs.append(Phdr(self, self.e_phoff + self.e_phentsize * i))

            self.shdrs = []
            for i in range(self.e_shnum):
                self.shdrs.append(Shdr(self, self.e_shoff + self.e_shentsize * i))
        return

    def read(self, size: int) -> bytes:
        return self.fd.read(size)

    def read_and_unpack(self, fmt: str) -> Tuple[Any, ...]:
        size = struct.calcsize(fmt)
        data = self.fd.read(size)
        return struct.unpack(fmt, data)

    def seek(self, off: int) -> None:
        self.fd.seek(off, 0)

    def __str__(self) -> str:
        return f"ELF('{self.path.absolute()}', {self.e_class.name}, {self.e_machine.name})"

    def __repr__(self) -> str:
        return f"ELF('{self.path.absolute()}', {self.e_class.name}, {self.e_machine.name})"

    @property
    def entry_point(self) -> int:
        return self.e_entry

    @classmethod
    def is_valid(cls, path: pathlib.Path) -> bool:
        return u32(path.open("rb").read(4), e = Endianness.BIG_ENDIAN) == Elf.ELF_MAGIC

    @classproperty
    @deprecated("use `Elf.Abi.ARM`")
    def ARM(cls) -> int : return Elf.Abi.ARM.value # pylint: disable=no-self-argument


class Phdr:
    class Type(enum.IntEnum):
        PT_NULL         = 0
        PT_LOAD         = 1
        PT_DYNAMIC      = 2
        PT_INTERP       = 3
        PT_NOTE         = 4
        PT_SHLIB        = 5
        PT_PHDR         = 6
        PT_TLS          = 7
        PT_LOOS         = 0x60000000
        PT_GNU_EH_FRAME = 0x6474e550
        PT_GNU_STACK    = 0x6474e551
        PT_GNU_RELRO    = 0x6474e552
        PT_GNU_PROPERTY = 0x6474e553
        PT_LOSUNW       = 0x6ffffffa
        PT_SUNWBSS      = 0x6ffffffa
        PT_SUNWSTACK    = 0x6ffffffb
        PT_HISUNW       = PT_HIOS         = 0x6fffffff
        PT_LOPROC       = 0x70000000
        PT_ARM_EIDX     = 0x70000001
        PT_MIPS_ABIFLAGS= 0x70000003
        PT_HIPROC       = 0x7fffffff
        UNKNOWN_PHDR    = 0xffffffff

        @classmethod
        def _missing_(cls, _:int) -> Type:
            return cls.UNKNOWN_PHDR

    class Flags(enum.IntFlag):
        PF_X            = 1
        PF_W            = 2
        PF_R            = 4

    p_type: "Phdr.Type"
    p_flags: "Phdr.Flags"
    p_offset: int
    p_vaddr: int
    p_paddr: int
    p_filesz: int
    p_memsz: int
    p_align: int

    def __init__(self, elf: Elf, off: int) -> None:
        if not elf:
            return
        elf.seek(off)
        self.offset = off
        endian = elf.e_endianness
        if elf.e_class == Elf.Class.ELF_64_BITS:
            p_type, p_flags, self.p_offset = elf.read_and_unpack(f"{endian}IIQ")
            self.p_vaddr, self.p_paddr = elf.read_and_unpack(f"{endian}QQ")
            self.p_filesz, self.p_memsz, self.p_align = elf.read_and_unpack(f"{endian}QQQ")
        else:
            p_type, self.p_offset = elf.read_and_unpack(f"{endian}II")
            self.p_vaddr, self.p_paddr = elf.read_and_unpack(f"{endian}II")
            self.p_filesz, self.p_memsz, p_flags, self.p_align = elf.read_and_unpack(f"{endian}IIII")

        self.p_type, self.p_flags = Phdr.Type(p_type), Phdr.Flags(p_flags)
        return

    def __str__(self) -> str:
        return (f"Phdr(offset={self.offset}, type={self.p_type.name}, flags={self.p_flags.name}, "
	            f"vaddr={self.p_vaddr}, paddr={self.p_paddr}, filesz={self.p_filesz}, "
	            f"memsz={self.p_memsz}, align={self.p_align})")


class Shdr:
    class Type(enum.IntEnum):
        SHT_NULL             = 0
        SHT_PROGBITS         = 1
        SHT_SYMTAB           = 2
        SHT_STRTAB           = 3
        SHT_RELA             = 4
        SHT_HASH             = 5
        SHT_DYNAMIC          = 6
        SHT_NOTE             = 7
        SHT_NOBITS           = 8
        SHT_REL              = 9
        SHT_SHLIB            = 10
        SHT_DYNSYM           = 11
        SHT_NUM	             = 12
        SHT_INIT_ARRAY       = 14
        SHT_FINI_ARRAY       = 15
        SHT_PREINIT_ARRAY    = 16
        SHT_GROUP            = 17
        SHT_SYMTAB_SHNDX     = 18
        SHT_LOOS             = 0x60000000
        SHT_GNU_ATTRIBUTES   = 0x6ffffff5
        SHT_GNU_HASH         = 0x6ffffff6
        SHT_GNU_LIBLIST      = 0x6ffffff7
        SHT_CHECKSUM         = 0x6ffffff8
        SHT_LOSUNW           = 0x6ffffffa
        SHT_SUNW_move        = 0x6ffffffa
        SHT_SUNW_COMDAT      = 0x6ffffffb
        SHT_SUNW_syminfo     = 0x6ffffffc
        SHT_GNU_verdef       = 0x6ffffffd
        SHT_GNU_verneed      = 0x6ffffffe
        SHT_GNU_versym       = 0x6fffffff
        SHT_LOPROC           = 0x70000000
        SHT_ARM_EXIDX        = 0x70000001
        SHT_X86_64_UNWIND    = 0x70000001
        SHT_ARM_ATTRIBUTES   = 0x70000003
        SHT_MIPS_OPTIONS     = 0x7000000d
        DT_MIPS_INTERFACE    = 0x7000002a
        SHT_HIPROC           = 0x7fffffff
        SHT_LOUSER           = 0x80000000
        SHT_HIUSER           = 0x8fffffff
        UNKNOWN_SHDR         = 0xffffffff

        @classmethod
        def _missing_(cls, _:int) -> Type:
            return cls.UNKNOWN_SHDR

    class Flags(enum.IntFlag):
        WRITE            = 1
        ALLOC            = 2
        EXECINSTR        = 4
        MERGE            = 0x10
        STRINGS          = 0x20
        INFO_LINK        = 0x40
        LINK_ORDER       = 0x80
        OS_NONCONFORMING = 0x100
        GROUP            = 0x200
        TLS              = 0x400
        COMPRESSED       = 0x800
        RELA_LIVEPATCH   = 0x00100000
        RO_AFTER_INIT    = 0x00200000
        ORDERED          = 0x40000000
        EXCLUDE          = 0x80000000
        UNKNOWN_FLAG     = 0xffffffff

        @classmethod
        def _missing_(cls, _:int):
            return cls.UNKNOWN_FLAG

    sh_name: int
    sh_type: "Shdr.Type"
    sh_flags: "Shdr.Flags"
    sh_addr: int
    sh_offset: int
    sh_size: int
    sh_link: int
    sh_info: int
    sh_addralign: int
    sh_entsize: int
    name: str

    def __init__(self, elf: Optional[Elf], off: int) -> None:
        if elf is None:
            return
        elf.seek(off)
        endian = elf.e_endianness
        if elf.e_class == Elf.Class.ELF_64_BITS:
            self.sh_name, sh_type, sh_flags = elf.read_and_unpack(f"{endian}IIQ")
            self.sh_addr, self.sh_offset = elf.read_and_unpack(f"{endian}QQ")
            self.sh_size, self.sh_link, self.sh_info = elf.read_and_unpack(f"{endian}QII")
            self.sh_addralign, self.sh_entsize = elf.read_and_unpack(f"{endian}QQ")
        else:
            self.sh_name, sh_type, sh_flags = elf.read_and_unpack(f"{endian}III")
            self.sh_addr, self.sh_offset = elf.read_and_unpack(f"{endian}II")
            self.sh_size, self.sh_link, self.sh_info = elf.read_and_unpack(f"{endian}III")
            self.sh_addralign, self.sh_entsize = elf.read_and_unpack(f"{endian}II")

        self.sh_type = Shdr.Type(sh_type)
        self.sh_flags = Shdr.Flags(sh_flags)
        stroff = elf.e_shoff + elf.e_shentsize * elf.e_shstrndx

        if elf.e_class == Elf.Class.ELF_64_BITS:
            elf.seek(stroff + 16 + 8)
            offset = u64(elf.read(8))
        else:
            elf.seek(stroff + 12 + 4)
            offset = u32(elf.read(4))
        elf.seek(offset + self.sh_name)
        self.name = ""
        while True:
            c = u8(elf.read(1))
            if c == 0:
                break
            self.name += chr(c)
        return

    def __str__(self) -> str:
        return (f"Shdr(name={self.name}, type={self.sh_type.name}, flags={self.sh_flags.name}, "
	            f"addr={self.sh_addr:#x}, offset={self.sh_offset}, size={self.sh_size}, link={self.sh_link}, "
	            f"info={self.sh_info}, addralign={self.sh_addralign}, entsize={self.sh_entsize})")


class Instruction:
    """GEF representation of a CPU instruction."""

    def __init__(self, address: int, location: str, mnemo: str, operands: List[str], opcodes: bytes) -> None:
        self.address, self.location, self.mnemonic, self.operands, self.opcodes = \
            address, location, mnemo, operands, opcodes
        return

    # Allow formatting an instruction with {:o} to show opcodes.
    # The number of bytes to display can be configured, e.g. {:4o} to only show 4 bytes of the opcodes
    def __format__(self, format_spec: str) -> str:
        if len(format_spec) == 0 or format_spec[-1] != "o":
            return str(self)

        if format_spec == "o":
            opcodes_len = len(self.opcodes)
        else:
            opcodes_len = int(format_spec[:-1])

        opcodes_text = "".join(f"{b:02x}" for b in self.opcodes[:opcodes_len])
        if opcodes_len < len(self.opcodes):
            opcodes_text += "..."
        return (f"{self.address:#10x} {opcodes_text:{opcodes_len * 2 + 3:d}s} {self.location:16} "
                f"{self.mnemonic:6} {', '.join(self.operands)}")

    def __str__(self) -> str:
        return f"{self.address:#10x} {self.location:16} {self.mnemonic:6} {', '.join(self.operands)}"

    def is_valid(self) -> bool:
        return "(bad)" not in self.mnemonic

    def size(self) -> int:
        return len(self.opcodes)


def titlify(text: str, color: Optional[str] = None, msg_color: Optional[str] = None) -> str:
    """Print a centered title."""
    _, cols = get_terminal_size()
    nb = (cols - len(text) - 2) // 2
    line_color = color or gef.config["theme.default_title_line"]
    text_color = msg_color or gef.config["theme.default_title_message"]

    msg = [Color.colorify(f"{HORIZONTAL_LINE * nb} ", line_color),
           Color.colorify(text, text_color),
           Color.colorify(f" {HORIZONTAL_LINE * nb}", line_color)]
    return "".join(msg)


def dbg(msg: str) -> None:
    if gef.config["gef.debug"] is True:
        gef_print(f"{Color.colorify('[=]', 'bold cyan')} {msg}")
    return


def err(msg: str) -> None:
    gef_print(f"{Color.colorify('[!]', 'bold red')} {msg}")
    return


def warn(msg: str) -> None:
    gef_print(f"{Color.colorify('[*]', 'bold yellow')} {msg}")
    return


def ok(msg: str) -> None:
    gef_print(f"{Color.colorify('[+]', 'bold green')} {msg}")
    return


def info(msg: str) -> None:
    gef_print(f"{Color.colorify('[+]', 'bold blue')} {msg}")
    return


def push_context_message(level: str, message: str) -> None:
    """Push the message to be displayed the next time the context is invoked."""
    if level not in ("error", "warn", "ok", "info"):
        err(f"Invalid level '{level}', discarding message")
        return
    gef.ui.context_messages.append((level, message))
    return


def show_last_exception() -> None:
    """Display the last Python exception."""

    def _show_code_line(fname: str, idx: int) -> str:
        fname = os.path.expanduser(os.path.expandvars(fname))
        with open(fname, "r") as f:
            __data = f.readlines()
        return __data[idx - 1] if 0 < idx < len(__data) else ""

    gef_print("")
    exc_type, exc_value, exc_traceback = sys.exc_info()

    gef_print(" Exception raised ".center(80, HORIZONTAL_LINE))
    gef_print(f"{Color.colorify(exc_type.__name__, 'bold underline red')}: {exc_value}")
    gef_print(" Detailed stacktrace ".center(80, HORIZONTAL_LINE))

    for fs in traceback.extract_tb(exc_traceback)[::-1]:
        filename, lineno, method, code = fs

        if not code or not code.strip():
            code = _show_code_line(filename, lineno)

        gef_print(f"""{DOWN_ARROW} File "{Color.yellowify(filename)}", line {lineno:d}, in {Color.greenify(method)}()""")
        gef_print(f"   {RIGHT_ARROW}    {code}")

    gef_print(" Version ".center(80, HORIZONTAL_LINE))
    gdb.execute("version full")
    gef_print(" Last 10 GDB commands ".center(80, HORIZONTAL_LINE))
    gdb.execute("show commands")
    gef_print(" Runtime environment ".center(80, HORIZONTAL_LINE))
    gef_print(f"* GDB: {gdb.VERSION}")
    gef_print(f"* Python: {sys.version_info.major:d}.{sys.version_info.minor:d}.{sys.version_info.micro:d} - {sys.version_info.releaselevel}")
    gef_print(f"* OS: {platform.system()} - {platform.release()} ({platform.machine()})")

    try:
        lsb_release = which("lsb_release")
        gdb.execute(f"!{lsb_release} -a")
    except FileNotFoundError:
        gef_print("lsb_release is missing, cannot collect additional debug information")

    gef_print(HORIZONTAL_LINE*80)
    gef_print("")
    return


def gef_pystring(x: bytes) -> str:
    """Returns a sanitized version as string of the bytes list given in input."""
    res = str(x, encoding="utf-8")
    substs = [("\n", "\\n"), ("\r", "\\r"), ("\t", "\\t"), ("\v", "\\v"), ("\b", "\\b"), ]
    for x, y in substs: res = res.replace(x, y)
    return res


def gef_pybytes(x: str) -> bytes:
    """Returns an immutable bytes list from the string given as input."""
    return bytes(str(x), encoding="utf-8")


@lru_cache()
def which(program: str) -> pathlib.Path:
    """Locate a command on the filesystem."""
    for path in os.environ["PATH"].split(os.pathsep):
        dirname = pathlib.Path(path)
        fpath = dirname / program
        if os.access(fpath, os.X_OK):
            return fpath

    raise FileNotFoundError(f"Missing file `{program}`")


def style_byte(b: int, color: bool = True) -> str:
    style = {
        "nonprintable": "yellow",
        "printable": "white",
        "00": "gray",
        "0a": "blue",
        "ff": "green",
    }
    sbyte = f"{b:02x}"
    if not color or gef.config["highlight.regex"]:
        return sbyte

    if sbyte in style:
        st = style[sbyte]
    elif chr(b) in (string.ascii_letters + string.digits + string.punctuation + " "):
        st = style.get("printable")
    else:
        st = style.get("nonprintable")
    if st:
        sbyte = Color.colorify(sbyte, st)
    return sbyte


def hexdump(source: ByteString, length: int = 0x10, separator: str = ".", show_raw: bool = False, show_symbol: bool = True, base: int = 0x00) -> str:
    """Return the hexdump of `src` argument.
    @param source *MUST* be of type bytes or bytearray
    @param length is the length of items per line
    @param separator is the default character to use if one byte is not printable
    @param show_raw if True, do not add the line nor the text translation
    @param base is the start address of the block being hexdump
    @return a string with the hexdump"""
    result = []
    align = gef.arch.ptrsize * 2 + 2 if is_alive() else 18

    for i in range(0, len(source), length):
        chunk = bytearray(source[i : i + length])
        hexa = " ".join([style_byte(b, color=not show_raw) for b in chunk])

        if show_raw:
            result.append(hexa)
            continue

        text = "".join([chr(b) if 0x20 <= b < 0x7F else separator for b in chunk])
        if show_symbol:
            sym = gdb_get_location_from_symbol(base + i)
            sym = "<{:s}+{:04x}>".format(*sym) if sym else ""
        else:
            sym = ""

        result.append(f"{base + i:#0{align}x} {sym}    {hexa:<{3 * length}}    {text}")
    return "\n".join(result)


def is_debug() -> bool:
    """Check if debug mode is enabled."""
    return gef.config["gef.debug"] is True


def hide_context() -> bool:
    """Helper function to hide the context pane."""
    gef.ui.context_hidden = True
    return True


def unhide_context() -> bool:
    """Helper function to unhide the context pane."""
    gef.ui.context_hidden = False
    return True


class DisableContextOutputContext:
    def __enter__(self) -> None:
        hide_context()
        return

    def __exit__(self, *exc: Any) -> None:
        unhide_context()
        return


class RedirectOutputContext:
    def __init__(self, to: str = "/dev/null") -> None:
        self.redirection_target_file = to
        return

    def __enter__(self) -> None:
        """Redirect all GDB output to `to_file` parameter. By default, `to_file` redirects to `/dev/null`."""
        gdb.execute("set logging overwrite")
        gdb.execute(f"set logging file {self.redirection_target_file}")
        gdb.execute("set logging redirect on")
        gdb.execute("set logging on")
        return

    def __exit__(self, *exc: Any) -> None:
        """Disable the output redirection, if any."""
        gdb.execute("set logging off")
        gdb.execute("set logging redirect off")
        return


def enable_redirect_output(to_file: str = "/dev/null") -> None:
    """Redirect all GDB output to `to_file` parameter. By default, `to_file` redirects to `/dev/null`."""
    gdb.execute("set logging overwrite")
    gdb.execute(f"set logging file {to_file}")
    gdb.execute("set logging redirect on")
    gdb.execute("set logging on")
    return


def disable_redirect_output() -> None:
    """Disable the output redirection, if any."""
    gdb.execute("set logging off")
    gdb.execute("set logging redirect off")
    return


def gef_makedirs(path: str, mode: int = 0o755) -> pathlib.Path:
    """Recursive mkdir() creation. If successful, return the absolute path of the directory created."""
    fpath = pathlib.Path(path)
    if not fpath.is_dir():
        fpath.mkdir(mode=mode, exist_ok=True, parents=True)
    return fpath.absolute()


@lru_cache()
def gdb_lookup_symbol(sym: str) -> Optional[Tuple[Optional[str], Optional[Tuple[gdb.Symtab_and_line, ...]]]]:
    """Fetch the proper symbol or None if not defined."""
    try:
        return gdb.decode_line(sym)[1]
    except gdb.error:
        return None


@lru_cache(maxsize=512)
def gdb_get_location_from_symbol(address: int) -> Optional[Tuple[str, int]]:
    """Retrieve the location of the `address` argument from the symbol table.
    Return a tuple with the name and offset if found, None otherwise."""
    # this is horrible, ugly hack and shitty perf...
    # find a *clean* way to get gdb.Location from an address
    sym = gdb.execute(f"info symbol {address:#x}", to_string=True)
    if sym.startswith("No symbol matches"):
        return None

    i = sym.find(" in section ")
    sym = sym[:i].split()
    name, offset = sym[0], 0
    if len(sym) == 3 and sym[2].isdigit():
        offset = int(sym[2])
    return name, offset


def gdb_disassemble(start_pc: int, **kwargs: int) -> Generator[Instruction, None, None]:
    """Disassemble instructions from `start_pc` (Integer). Accepts the following named parameters:
    - `end_pc` (Integer) only instructions whose start address fall in the interval from start_pc to end_pc are returned.
    - `count` (Integer) list at most this many disassembled instructions
    If `end_pc` and `count` are not provided, the function will behave as if `count=1`.
    Return an iterator of Instruction objects
    """
    frame = gdb.selected_frame()
    arch = frame.architecture()

    for insn in arch.disassemble(start_pc, **kwargs):
        address = insn["addr"]
        asm = insn["asm"].rstrip().split(None, 1)
        if len(asm) > 1:
            mnemo, operands = asm
            operands = operands.split(",")
        else:
            mnemo, operands = asm[0], []

        loc = gdb_get_location_from_symbol(address)
        location = "<{}+{}>".format(*loc) if loc else ""

        opcodes = gef.memory.read(insn["addr"], insn["length"])

        yield Instruction(address, location, mnemo, operands, opcodes)


def gdb_get_nth_previous_instruction_address(addr: int, n: int) -> Optional[int]:
    """Return the address (Integer) of the `n`-th instruction before `addr`."""
    # fixed-length ABI
    if gef.arch.instruction_length:
        return max(0, addr - n * gef.arch.instruction_length)

    # variable-length ABI
    cur_insn_addr = gef_current_instruction(addr).address

    # we try to find a good set of previous instructions by "guessing" disassembling backwards
    # the 15 comes from the longest instruction valid size
    for i in range(15 * n, 0, -1):
        try:
            insns = list(gdb_disassemble(addr - i, end_pc=cur_insn_addr))
        except gdb.MemoryError:
            # this is because we can hit an unmapped page trying to read backward
            break

        # 1. check that the disassembled instructions list size can satisfy
        if len(insns) < n + 1:  # we expect the current instruction plus the n before it
            continue

        # If the list of instructions is longer than what we need, then we
        # could get lucky and already have more than what we need, so slice down
        insns = insns[-n - 1 :]

        # 2. check that the sequence ends with the current address
        if insns[-1].address != cur_insn_addr:
            continue

        # 3. check all instructions are valid
        if all(insn.is_valid() for insn in insns):
            return insns[0].address

    return None


def gdb_get_nth_next_instruction_address(addr: int, n: int) -> int:
    """Return the address (Integer) of the `n`-th instruction after `addr`."""
    # fixed-length ABI
    if gef.arch.instruction_length:
        return addr + n * gef.arch.instruction_length

    # variable-length ABI
    insn = list(gdb_disassemble(addr, count=n))[-1]
    return insn.address


def gef_instruction_n(addr: int, n: int) -> Instruction:
    """Return the `n`-th instruction after `addr` as an Instruction object."""
    return list(gdb_disassemble(addr, count=n + 1))[n]


def gef_get_instruction_at(addr: int) -> Instruction:
    """Return the full Instruction found at the specified address."""
    insn = next(gef_disassemble(addr, 1))
    return insn


def gef_current_instruction(addr: int) -> Instruction:
    """Return the current instruction as an Instruction object."""
    return gef_instruction_n(addr, 0)


def gef_next_instruction(addr: int) -> Instruction:
    """Return the next instruction as an Instruction object."""
    return gef_instruction_n(addr, 1)


def gef_disassemble(addr: int, nb_insn: int, nb_prev: int = 0) -> Generator[Instruction, None, None]:
    """Disassemble `nb_insn` instructions after `addr` and `nb_prev` before `addr`.
    Return an iterator of Instruction objects."""
    nb_insn = max(1, nb_insn)

    if nb_prev:
        start_addr = gdb_get_nth_previous_instruction_address(addr, nb_prev)
        if start_addr:
            for insn in gdb_disassemble(start_addr, count=nb_prev):
                if insn.address == addr: break
                yield insn

    for insn in gdb_disassemble(addr, count=nb_insn):
        yield insn


def gef_execute_external(command: Sequence[str], as_list: bool = False, **kwargs: Any) -> Union[str, List[str]]:
    """Execute an external command and return the result."""
    res = subprocess.check_output(command, stderr=subprocess.STDOUT, shell=kwargs.get("shell", False))
    return [gef_pystring(_) for _ in res.splitlines()] if as_list else gef_pystring(res)


def gef_execute_gdb_script(commands: str) -> None:
    """Execute the parameter `source` as GDB command. This is done by writing `commands` to
    a temporary file, which is then executed via GDB `source` command. The tempfile is then deleted."""
    fd, fname = tempfile.mkstemp(suffix=".gdb", prefix="gef_")
    with os.fdopen(fd, "w") as f:
        f.write(commands)
        f.flush()

    fname = pathlib.Path(fname)
    if fname.is_file() and os.access(fname, os.R_OK):
        gdb.execute(f"source {fname}")
        fname.unlink()
    return


@lru_cache()
def get_arch() -> str:
    """Return the binary's architecture."""
    if is_alive():
        arch = gdb.selected_frame().architecture()
        return arch.name()

    arch_str = gdb.execute("show architecture", to_string=True).strip()
    pat = "The target architecture is set automatically (currently "
    if arch_str.startswith(pat):
        arch_str = arch_str[len(pat):].rstrip(")")
        return arch_str

    pat = "The target architecture is assumed to be "
    if arch_str.startswith(pat):
        return arch_str[len(pat):]

    pat = "The target architecture is set to "
    if arch_str.startswith(pat):
        # GDB version >= 10.1
        if '"auto"' in arch_str:
            return re.findall(r"currently \"(.+)\"", arch_str)[0]
        return re.findall(r"\"(.+)\"", arch_str)[0]

    # Unknown, we throw an exception to be safe
    raise RuntimeError(f"Unknown architecture: {arch_str}")


@deprecated("Use `gef.binary.entry_point` instead")
def get_entry_point() -> Optional[int]:
    """Return the binary entry point."""
    return gef.binary.entry_point if gef.binary else None


@deprecated("Prefer `gef.arch.endianness == Endianness.BIG_ENDIAN`")
def is_big_endian() -> bool:
    return gef.arch.endianness == Endianness.BIG_ENDIAN


@deprecated("gef.arch.endianness == Endianness.LITTLE_ENDIAN")
def is_little_endian() -> bool:
    return gef.arch.endianness == Endianness.LITTLE_ENDIAN


def flags_to_human(reg_value: int, value_table: Dict[int, str]) -> str:
    """Return a human readable string showing the flag states."""
    flags = []
    for bit_index, name in value_table.items():
        flags.append(Color.boldify(name.upper()) if reg_value & (1<<bit_index) != 0 else name.lower())
    return f"[{' '.join(flags)}]"


@lru_cache()
def get_section_base_address(name: str) -> Optional[int]:
    section = process_lookup_path(name)
    return section.start if section else None


@lru_cache()
def get_zone_base_address(name: str) -> Optional[int]:
    zone = file_lookup_name_path(name, get_filepath())
    return zone.zone_start if zone else None


#
# Architecture classes
#
@deprecated("Using the decorator `register_architecture` is unecessary")
def register_architecture(cls: Type["Architecture"]) -> Type["Architecture"]:
    return cls

class ArchitectureBase:
    """Class decorator for declaring an architecture to GEF."""
    aliases: Union[Tuple[()], Tuple[Union[str, Elf.Abi], ...]] = ()

    def __init_subclass__(cls: Type["ArchitectureBase"], **kwargs):
        global __registered_architectures__
        super().__init_subclass__(**kwargs)
        for key in getattr(cls, "aliases"):
            if issubclass(cls, Architecture):
                __registered_architectures__[key] = cls
        return


class Architecture(ArchitectureBase):
    """Generic metaclass for the architecture supported by GEF."""

    # Mandatory defined attributes by inheriting classes
    arch: str
    mode: str
    all_registers: Union[Tuple[()], Tuple[str, ...]]
    nop_insn: bytes
    return_register: str
    flag_register: Optional[str]
    instruction_length: Optional[int]
    flags_table: Dict[int, str]
    syscall_register: Optional[str]
    syscall_instructions: Union[Tuple[()], Tuple[str, ...]]
    function_parameters: Union[Tuple[()], Tuple[str, ...]]

    # Optionally defined attributes
    _ptrsize: Optional[int] = None
    _endianness: Optional[Endianness] = None
    special_registers: Union[Tuple[()], Tuple[str, ...]] = ()

    def __init_subclass__(cls, **kwargs):
        super().__init_subclass__(**kwargs)
        attributes = ("arch", "mode", "aliases", "all_registers", "nop_insn",
             "return_register", "flag_register", "instruction_length", "flags_table",
             "function_parameters",)
        if not all(map(lambda x: hasattr(cls, x), attributes)):
            raise NotImplementedError

    def __str__(self) -> str:
        return f"Architecture({self.arch}, {self.mode or 'None'}, {repr(self.endianness)})"

    @staticmethod
    def supports_gdb_arch(gdb_arch: str) -> Optional[bool]:
        """If implemented by a child `Architecture`, this function dictates if the current class
        supports the loaded ELF file (which can be accessed via `gef.binary`). This callback
        function will override any assumption made by GEF to determine the architecture."""
        return None

    def flag_register_to_human(self, val: Optional[int] = None) -> str:
        raise NotImplementedError

    def is_call(self, insn: Instruction) -> bool:
        raise NotImplementedError

    def is_ret(self, insn: Instruction) -> bool:
        raise NotImplementedError

    def is_conditional_branch(self, insn: Instruction) -> bool:
        raise NotImplementedError

    def is_branch_taken(self, insn: Instruction) -> Tuple[bool, str]:
        raise NotImplementedError

    def get_ra(self, insn: Instruction, frame: "gdb.Frame") -> Optional[int]:
        raise NotImplementedError

    @classmethod
    def mprotect_asm(cls, addr: int, size: int, perm: Permission) -> str:
        raise NotImplementedError

    def reset_caches(self) -> None:
        self.__get_register_for_selected_frame.cache_clear()
        return

    def __get_register(self, regname: str) -> int:
        """Return a register's value."""
        curframe = gdb.selected_frame()
        key = curframe.pc() ^ int(curframe.read_register('sp')) # todo: check when/if gdb.Frame implements `level()`
        return self.__get_register_for_selected_frame(regname, key)

    @lru_cache()
    def __get_register_for_selected_frame(self, regname: str, hash_key: int) -> int:
        # 1st chance
        try:
            return parse_address(regname)
        except gdb.error:
            pass

        # 2nd chance - if an exception, propagate it
        regname = regname.lstrip("$")
        value = gdb.selected_frame().read_register(regname)
        return int(value)

    def register(self, name: str) -> int:
        if not is_alive():
            raise gdb.error("No debugging session active")
        return self.__get_register(name)

    @property
    def registers(self) -> Generator[str, None, None]:
        yield from self.all_registers

    @property
    def pc(self) -> int:
        return self.register("$pc")

    @property
    def sp(self) -> int:
        return self.register("$sp")

    @property
    def fp(self) -> int:
        return self.register("$fp")

    @property
    def ptrsize(self) -> int:
        if not self._ptrsize:
            res = cached_lookup_type("size_t")
            if res is not None:
                self._ptrsize = res.sizeof
            else:
                self._ptrsize = gdb.parse_and_eval("$pc").type.sizeof
        return self._ptrsize

    @property
    def endianness(self) -> Endianness:
        if not self._endianness:
            output = gdb.execute("show endian", to_string=True).strip().lower()
            if "little endian" in output:
                self._endianness = Endianness.LITTLE_ENDIAN
            elif "big endian" in output:
                self._endianness = Endianness.BIG_ENDIAN
            else:
                raise OSError(f"No valid endianess found in '{output}'")
        return self._endianness

    def get_ith_parameter(self, i: int, in_func: bool = True) -> Tuple[str, Optional[int]]:
        """Retrieves the correct parameter used for the current function call."""
        reg = self.function_parameters[i]
        val = self.register(reg)
        key = reg
        return key, val


class GenericArchitecture(Architecture):
    arch = "Generic"
    mode = ""
    aliases = ("GenericArchitecture",)
    all_registers = ()
    instruction_length = 0
    return_register = ""
    function_parameters = ()
    syscall_register = ""
    syscall_instructions = ()
    nop_insn = b""
    flag_register = None
    flags_table = {}


class ARM(Architecture):
    aliases = ("ARM", Elf.Abi.ARM)
    arch = "ARM"
    all_registers = ("$r0", "$r1", "$r2", "$r3", "$r4", "$r5", "$r6",
                     "$r7", "$r8", "$r9", "$r10", "$r11", "$r12", "$sp",
                     "$lr", "$pc", "$cpsr",)

    # https://infocenter.arm.com/help/index.jsp?topic=/com.arm.doc.dui0041c/Caccegih.html
    nop_insn = b"\x01\x10\xa0\xe1" # mov r1, r1
    return_register = "$r0"
    flag_register: str = "$cpsr"
    flags_table = {
        31: "negative",
        30: "zero",
        29: "carry",
        28: "overflow",
        7: "interrupt",
        6: "fast",
        5: "thumb",
    }
    function_parameters = ("$r0", "$r1", "$r2", "$r3")
    syscall_register = "$r7"
    syscall_instructions = ("swi NR")
    _endianness = Endianness.LITTLE_ENDIAN

    def is_thumb(self) -> bool:
        """Determine if the machine is currently in THUMB mode."""
        return is_alive() and (self.cpsr & (1 << 5) == 32)

    @property
    def pc(self) -> Optional[int]:
        pc = gef.arch.register("$pc")
        if self.is_thumb():
            pc += 1
        return pc

    @property
    def cpsr(self) -> int:
        if not is_alive():
            raise RuntimeError("Cannot get CPSR, program not started?")
        return gef.arch.register(self.flag_register)

    @property
    def mode(self) -> str:
        return "THUMB" if self.is_thumb() else "ARM"

    @property
    def instruction_length(self) -> Optional[int]:
        # Thumb instructions have variable-length (2 or 4-byte)
        return None if self.is_thumb() else 4

    @property
    def ptrsize(self) -> int:
        return 4

    def is_call(self, insn: Instruction) -> bool:
        mnemo = insn.mnemonic
        call_mnemos = {"bl", "blx"}
        return mnemo in call_mnemos

    def is_ret(self, insn: Instruction) -> bool:
        pop_mnemos = {"pop"}
        branch_mnemos = {"bl", "bx"}
        write_mnemos = {"ldr", "add"}
        if insn.mnemonic in pop_mnemos:
            return insn.operands[-1] == " pc}"
        if insn.mnemonic in branch_mnemos:
            return insn.operands[-1] == "lr"
        if insn.mnemonic in write_mnemos:
            return insn.operands[0] == "pc"
        return False

    def flag_register_to_human(self, val: Optional[int] = None) -> str:
        # https://www.botskool.com/user-pages/tutorials/electronics/arm-7-tutorial-part-1
        if val is None:
            reg = self.flag_register
            val = gef.arch.register(reg)
        return flags_to_human(val, self.flags_table)

    def is_conditional_branch(self, insn: Instruction) -> bool:
        conditions = {"eq", "ne", "lt", "le", "gt", "ge", "vs", "vc", "mi", "pl", "hi", "ls", "cc", "cs"}
        return insn.mnemonic[-2:] in conditions

    def is_branch_taken(self, insn: Instruction) -> Tuple[bool, str]:
        mnemo = insn.mnemonic
        # ref: https://www.davespace.co.uk/arm/introduction-to-arm/conditional.html
        flags = dict((self.flags_table[k], k) for k in self.flags_table)
        val = gef.arch.register(self.flag_register)
        taken, reason = False, ""

        if mnemo.endswith("eq"): taken, reason = bool(val&(1<<flags["zero"])), "Z"
        elif mnemo.endswith("ne"): taken, reason = not bool(val&(1<<flags["zero"])), "!Z"
        elif mnemo.endswith("lt"):
            taken, reason = bool(val&(1<<flags["negative"])) != bool(val&(1<<flags["overflow"])), "N!=V"
        elif mnemo.endswith("le"):
            taken, reason = bool(val&(1<<flags["zero"])) or \
                bool(val&(1<<flags["negative"])) != bool(val&(1<<flags["overflow"])), "Z || N!=V"
        elif mnemo.endswith("gt"):
            taken, reason = bool(val&(1<<flags["zero"])) == 0 and \
                bool(val&(1<<flags["negative"])) == bool(val&(1<<flags["overflow"])), "!Z && N==V"
        elif mnemo.endswith("ge"):
            taken, reason = bool(val&(1<<flags["negative"])) == bool(val&(1<<flags["overflow"])), "N==V"
        elif mnemo.endswith("vs"): taken, reason = bool(val&(1<<flags["overflow"])), "V"
        elif mnemo.endswith("vc"): taken, reason = not val&(1<<flags["overflow"]), "!V"
        elif mnemo.endswith("mi"):
            taken, reason = bool(val&(1<<flags["negative"])), "N"
        elif mnemo.endswith("pl"):
            taken, reason = not val&(1<<flags["negative"]), "N==0"
        elif mnemo.endswith("hi"):
            taken, reason = bool(val&(1<<flags["carry"])) and not bool(val&(1<<flags["zero"])), "C && !Z"
        elif mnemo.endswith("ls"):
            taken, reason = not val&(1<<flags["carry"]) or bool(val&(1<<flags["zero"])), "!C || Z"
        elif mnemo.endswith("cs"): taken, reason = bool(val&(1<<flags["carry"])), "C"
        elif mnemo.endswith("cc"): taken, reason = not val&(1<<flags["carry"]), "!C"
        return taken, reason

    def get_ra(self, insn: Instruction, frame: "gdb.Frame") -> int:
        ra = None
        if self.is_ret(insn):
            # If it's a pop, we have to peek into the stack, otherwise use lr
            if insn.mnemonic == "pop":
                ra_addr = gef.arch.sp + (len(insn.operands)-1) * self.ptrsize
                ra = to_unsigned_long(dereference(ra_addr))
            elif insn.mnemonic == "ldr":
                return to_unsigned_long(dereference(gef.arch.sp))
            else:  # 'bx lr' or 'add pc, lr, #0'
                return gef.arch.register("$lr")
        elif frame.older():
            ra = frame.older().pc()
        return ra


def copy_to_clipboard(data: bytes) -> None:
    """Helper function to submit data to the clipboard"""
    if sys.platform == "linux":
        xclip = which("xclip")
        prog = [xclip, "-selection", "clipboard", "-i"]
    elif sys.platform == "darwin":
        pbcopy = which("pbcopy")
        prog = [pbcopy]
    else:
        raise NotImplementedError("copy: Unsupported OS")

    with subprocess.Popen(prog, stdin=subprocess.PIPE) as p:
        p.stdin.write(data)
        p.stdin.close()
        p.wait()
    return


def use_stdtype() -> str:
    if is_32bit(): return "uint32_t"
    return "uint16_t"


def use_default_type() -> str:
    if is_32bit(): return "unsigned int"
    return "unsigned short"


def to_unsigned_long(v: gdb.Value) -> int:
    """Cast a gdb.Value to unsigned long."""
    mask = (1 << 64) - 1
    return int(v.cast(gdb.Value(mask).type)) & mask


def get_path_from_info_proc() -> Optional[str]:
    for x in gdb.execute("info proc", to_string=True).splitlines():
        if x.startswith("exe = "):
            return x.split(" = ")[1].replace("'", "")
    return None


@deprecated("Use `gef.session.os`")
def get_os() -> str:
    return gef.session.os


@lru_cache()
def is_qemu() -> bool:
    if not is_remote_debug():
        return False
    response = gdb.execute('maintenance packet Qqemu.sstepbits', to_string=True, from_tty=False)
    return 'ENABLE=' in response


@lru_cache()
def is_qemu_usermode() -> bool:
    if not is_qemu():
        return False
    response = gdb.execute('maintenance packet QOffsets', to_string=True, from_tty=False)
    return "Text=" in response


@lru_cache()
def is_qemu_system() -> bool:
    if not is_qemu():
        return False
    response = gdb.execute('maintenance packet QOffsets', to_string=True, from_tty=False)
    return 'received: ""' in response


def get_filepath() -> Optional[str]:
    """Return the local absolute path of the file currently debugged."""
    if gef.session.remote:
        return str(gef.session.remote.lfile.absolute())
    if gef.session.file:
        return str(gef.session.file.absolute())
    return None


def get_function_length(sym: str) -> int:
    """Attempt to get the length of the raw bytes of a function."""
    dis = gdb.execute(f"disassemble {sym}", to_string=True).splitlines()
    start_addr = int(dis[1].split()[0], 16)
    end_addr = int(dis[-2].split()[0], 16)
    return end_addr - start_addr


@lru_cache()
def get_info_files() -> List[Zone]:
    """Retrieve all the files loaded by debuggee."""
    lines = gdb.execute("info files", to_string=True).splitlines()
    infos = []
    for line in lines:
        line = line.strip()
        if not line:
            break

        if not line.startswith("0x"):
            continue

        blobs = [x.strip() for x in line.split(" ")]
        addr_start = int(blobs[0], 16)
        addr_end = int(blobs[2], 16)
        section_name = blobs[4]

        if len(blobs) == 7:
            filename = blobs[6]
        else:
            filename = get_filepath()

        infos.append(Zone(section_name, addr_start, addr_end, filename))
    return infos


def process_lookup_address(address: int) -> Optional[Section]:
    """Look up for an address in memory.
    Return an Address object if found, None otherwise."""
    if not is_alive():
        err("Process is not running")
        return None

    for sect in gef.memory.maps:
        if sect.start <= address < sect.end:
            return sect

    return None


@lru_cache()
def process_lookup_path(name: str, perm: Permission = Permission.ALL) -> Optional[Section]:
    """Look up for a path in the process memory mapping.
    Return a Section object if found, None otherwise."""
    if not is_alive():
        err("Process is not running")
        return None

    for sect in gef.memory.maps:
        if name in sect.name and sect.permission & perm:
            return sect

    return None


@lru_cache()
def file_lookup_name_path(name: str, path: str) -> Optional[Zone]:
    """Look up a file by name and path.
    Return a Zone object if found, None otherwise."""
    for xfile in get_info_files():
        if path == xfile.filename and name == xfile.name:
            return xfile
    return None


@lru_cache()
def file_lookup_address(address: int) -> Optional[Zone]:
    """Look up for a file by its address.
    Return a Zone object if found, None otherwise."""
    for info in get_info_files():
        if info.zone_start <= address < info.zone_end:
            return info
    return None


@lru_cache()
def lookup_address(address: int) -> Address:
    """Try to find the address in the process address space.
    Return an Address object, with validity flag set based on success."""
    sect = process_lookup_address(address)
    info = file_lookup_address(address)
    if sect is None and info is None:
        # i.e. there is no info on this address
        return Address(value=address, valid=False)
    return Address(value=address, section=sect, info=info)


def xor(data: ByteString, key: str) -> bytearray:
    """Return `data` xor-ed with `key`."""
    key_raw = binascii.unhexlify(key.lstrip("0x"))
    return bytearray(x ^ y for x, y in zip(data, itertools.cycle(key_raw)))


def is_hex(pattern: str) -> bool:
    """Return whether provided string is a hexadecimal value."""
    if not pattern.lower().startswith("0x"):
        return False
    return len(pattern) % 2 == 0 and all(c in string.hexdigits for c in pattern[2:])


def continue_handler(_: "gdb.Event") -> None:
    """GDB event handler for new object continue cases."""
    return


def hook_stop_handler(_: "gdb.StopEvent") -> None:
    """GDB event handler for stop cases."""
    reset_all_caches()
    gdb.execute("context")
    return


def new_objfile_handler(evt: "gdb.Event") -> None:
    """GDB event handler for new object file cases."""
    reset_all_caches()
    try:
        target = pathlib.Path( evt.new_objfile.filename if evt else gdb.current_progspace().filename)
        FileFormatClasses = list(filter(lambda fmtcls: fmtcls.is_valid(target), __registered_file_formats__))
        GuessedFileFormatClass : Type[FileFormat] = FileFormatClasses.pop() if len(FileFormatClasses) else Elf
        binary = GuessedFileFormatClass(target)
        if not gef.binary:
            gef.binary = binary
            reset_architecture()
        else:
            gef.session.modules.append(binary)
    except FileNotFoundError as fne:
        warn(f"Failed to find objfile or not a valid file format: {str(fne)}")
    except RuntimeError as re:
        warn(f"Not a valid file format: {str(re)}")
    return


def exit_handler(_: "gdb.ExitedEvent") -> None:
    """GDB event handler for exit cases."""
    global gef
    reset_all_caches()
    gef.session.qemu_mode = False
    if gef.session.remote:
        # make sure the tempdir is trashed
        del(gef.session.remote)
        gef.session.remote = None
    return


def memchanged_handler(_: "gdb.MemoryChangedEvent") -> None:
    """GDB event handler for mem changes cases."""
    reset_all_caches()
    return


def regchanged_handler(_: "gdb.RegisterChangedEvent") -> None:
    """GDB event handler for reg changes cases."""
    reset_all_caches()
    return


def get_terminal_size() -> Tuple[int, int]:
    """Return the current terminal size."""
    if is_debug():
        return 600, 100

    if platform.system() == "Windows":
        from ctypes import create_string_buffer, windll
        hStdErr = -12
        herr = windll.kernel32.GetStdHandle(hStdErr)
        csbi = create_string_buffer(22)
        res = windll.kernel32.GetConsoleScreenBufferInfo(herr, csbi)
        if res:
            _, _, _, _, _, left, top, right, bottom, _, _ = struct.unpack("hhhhHhhhhhh", csbi.raw)
            tty_columns = right - left + 1
            tty_rows = bottom - top + 1
            return tty_rows, tty_columns
        else:
            return 600, 100
    else:
        import fcntl
        import termios
        try:
            tty_rows, tty_columns = struct.unpack("hh", fcntl.ioctl(1, termios.TIOCGWINSZ, "1234")) # type: ignore
            return tty_rows, tty_columns
        except OSError:
            return 600, 100


@lru_cache()
def is_32bit() -> bool:
    """Checks if current target is 32bit."""
    return gef.arch.ptrsize == 4


@lru_cache()
def is_arch(arch: Elf.Abi) -> bool:
    return arch in gef.arch.aliases


def reset_architecture(arch: Optional[str] = None) -> None:
    """Sets the current architecture.
    If an architecture is explicitly specified by parameter, try to use that one. If this fails, an `OSError`
    exception will occur.
    If no architecture is specified, then GEF will attempt to determine automatically based on the current
    ELF target. If this fails, an `OSError` exception will occur.
    """
    global gef
    arches = __registered_architectures__

    # check if the architecture is forced by parameter
    if arch:
        try:
            gef.arch = arches[arch]()
        except KeyError:
            raise OSError(f"Specified arch {arch.upper()} is not supported")

    gdb_arch = get_arch()

    preciser_arch = next((a for a in arches.values() if a.supports_gdb_arch(gdb_arch)), None)
    if preciser_arch:
        gef.arch = preciser_arch()
        return

    # last resort, use the info from elf header to find it from the known architectures
    try:
        arch_name = gef.binary.e_machine if gef.binary else gdb_arch
        gef.arch = arches[arch_name]()
    except KeyError:
        raise OSError(f"CPU type is currently not supported: {get_arch()}")
    return


@lru_cache()
def cached_lookup_type(_type: str) -> Optional[gdb.Type]:
    try:
        return gdb.lookup_type(_type).strip_typedefs()
    except RuntimeError:
        return None


@deprecated("Use `gef.arch.ptrsize` instead")
def get_memory_alignment(in_bits: bool = False) -> int:
    """Try to determine the size of a pointer on this system.
    First, try to parse it out of the ELF header.
    Next, use the size of `size_t`.
    Finally, try the size of $pc.
    If `in_bits` is set to True, the result is returned in bits, otherwise in
    bytes."""
    res = cached_lookup_type("size_t")
    if res is not None:
        return res.sizeof if not in_bits else res.sizeof * 8

    try:
        return gdb.parse_and_eval("$pc").type.sizeof
    except:
        pass

    raise OSError("GEF is running under an unsupported mode")


def clear_screen(tty: str = "") -> None:
    """Clear the screen."""
    global gef
    if not tty:
        gdb.execute("shell clear -x")
        return

    # Since the tty can be closed at any time, a PermissionError exception can
    # occur when `clear_screen` is called. We handle this scenario properly
    try:
        with open(tty, "wt") as f:
            f.write("\x1b[H\x1b[J")
    except PermissionError:
        gef.ui.redirect_fd = None
        gef.config["context.redirect"] = ""
    return


def format_address(addr: int) -> str:
    """Format the address according to its size."""
    return f"0x{addr:08x}"


def format_address_spaces(addr: int, left: bool = True) -> str:
    """Format the address according to its size, but with spaces instead of zeroes."""
    width = gef.arch.ptrsize * 2 + 2
    addr = align_address(addr)

    if not left:
        return f"{addr:#x}".rjust(width)

    return f"{addr:#x}".ljust(width)


def align_address(address: int) -> int:
    """Align the provided address to the process's native length."""
    return address & 0xFFFFFFFF


def align_address_to_size(address: int, align: int) -> int:
    """Align the address to the given size."""
    return address + ((align - (address % align)) % align)


def align_address_to_page(address: int) -> int:
    """Align the address to a page."""
    a = align_address(address) >> DEFAULT_PAGE_ALIGN_SHIFT
    return a << DEFAULT_PAGE_ALIGN_SHIFT


def parse_address(address: str) -> int:
    """Parse an address and return it as an Integer."""
    if is_hex(address):
        return int(address, 16)
    return to_unsigned_long(gdb.parse_and_eval(address))


def is_remote_debug() -> bool:
    """"Return True is the current debugging session is running through GDB remote session."""
    return gef.session.remote is not None


def de_bruijn(alphabet: bytes, n: int) -> Generator[str, None, None]:
    """De Bruijn sequence for alphabet and subsequences of length n (for compat. w/ pwnlib)."""
    k = len(alphabet)
    a = [0] * k * n

    def db(t: int, p: int) -> Generator[str, None, None]:
        if t > n:
            if n % p == 0:
                for j in range(1, p + 1):
                    yield alphabet[a[j]]
        else:
            a[t] = a[t - p]
            yield from db(t + 1, p)

            for j in range(a[t - p] + 1, k):
                a[t] = j
                yield from db(t + 1, t)

    return db(1, 1)


def generate_cyclic_pattern(length: int, cycle: int = 4) -> bytearray:
    """Create a `length` byte bytearray of a de Bruijn cyclic pattern."""
    charset = bytearray(b"abcdefghijklmnopqrstuvwxyz")
    return bytearray(itertools.islice(de_bruijn(charset, cycle), length))


def safe_parse_and_eval(value: str) -> Optional["gdb.Value"]:
    """GEF wrapper for gdb.parse_and_eval(): this function returns None instead of raising
    gdb.error if the eval failed."""
    try:
        return gdb.parse_and_eval(value)
    except gdb.error:
        pass
    return None


@lru_cache()
def dereference(addr: int) -> Optional["gdb.Value"]:
    """GEF wrapper for gdb dereference function."""
    try:
        ulong_t = cached_lookup_type(use_stdtype()) or \
                  cached_lookup_type(use_default_type()) or \
                  cached_lookup_type(use_golang_type()) or \
                  cached_lookup_type(use_rust_type())
        unsigned_long_type = ulong_t.pointer()
        res = gdb.Value(addr).cast(unsigned_long_type).dereference()
        # GDB does lazy fetch by default so we need to force access to the value
        res.fetch_lazy()
        return res
    except gdb.MemoryError:
        pass
    return None


def gef_convenience(value: Union[str, bytes]) -> str:
    """Defines a new convenience value."""
    global gef
    var_name = f"$_gef{gef.session.convenience_vars_index:d}"
    gef.session.convenience_vars_index += 1
    if isinstance(value, str):
        gdb.execute(f"""set {var_name} = "{value}" """)
    elif isinstance(value, bytes):
        value_as_array = "{" + ", ".join(["%#.02x" % x for x in value]) + "}"
        gdb.execute(f"""set {var_name} = {value_as_array} """)
    else:
        raise TypeError
    return var_name


def parse_string_range(s: str) -> Iterator[int]:
    """Parses an address range (e.g. 0x400000-0x401000)"""
    addrs = s.split("-")
    return map(lambda x: int(x, 16), addrs)


@lru_cache()
def is_syscall(instruction: Union[Instruction,int]) -> bool:
    """Checks whether an instruction or address points to a system call."""
    if isinstance(instruction, int):
        instruction = gef_current_instruction(instruction)
    insn_str = instruction.mnemonic
    if len(instruction.operands):
        insn_str += f" {', '.join(instruction.operands)}"
    return insn_str in gef.arch.syscall_instructions


#
# Deprecated API
#

@deprecated("Use `gef.session.pie_breakpoints[num]`")
def gef_get_pie_breakpoint(num: int) -> "PieVirtualBreakpoint":
    return gef.session.pie_breakpoints[num]


@deprecated("Use `str(gef.arch.endianness)` instead")
def endian_str() -> str:
    return str(gef.arch.endianness)


@deprecated("Use `gef.config[key]`")
def get_gef_setting(name: str) -> Any:
    return gef.config[name]


@deprecated("Use `gef.config[key] = value`")
def set_gef_setting(name: str, value: Any) -> None:
    gef.config[name] = value
    return


@deprecated("Use `gef.session.pagesize`")
def gef_getpagesize() -> int:
    return gef.session.pagesize


@deprecated("Use `gef.session.pid`")
def get_pid() -> int:
    return gef.session.pid


@deprecated("Use `gef.session.file.name`")
def get_filename() -> str:
    return gef.session.file.name


@deprecated("Use `gef.arch.register(regname)`")
def get_register(regname) -> Optional[int]:
    return gef.arch.register(regname)


@deprecated("Use `gef.memory.maps`")
def get_process_maps() -> List[Section]:
    return gef.memory.maps


@deprecated("Use `reset_architecture`")
def set_arch(arch: Optional[str] = None, _: Optional[str] = None) -> None:
    return reset_architecture(arch)

#
# GDB event hooking
#

@only_if_events_supported("cont")
def gef_on_continue_hook(func: Callable[["gdb.ThreadEvent"], None]) -> None:
    gdb.events.cont.connect(func)


@only_if_events_supported("cont")
def gef_on_continue_unhook(func: Callable[["gdb.ThreadEvent"], None]) -> None:
    gdb.events.cont.disconnect(func)


@only_if_events_supported("stop")
def gef_on_stop_hook(func: Callable[["gdb.StopEvent"], None]) -> None:
    gdb.events.stop.connect(func)


@only_if_events_supported("stop")
def gef_on_stop_unhook(func: Callable[["gdb.StopEvent"], None]) -> None:
    gdb.events.stop.disconnect(func)


@only_if_events_supported("exited")
def gef_on_exit_hook(func: Callable[["gdb.ExitedEvent"], None]) -> None:
    gdb.events.exited.connect(func)


@only_if_events_supported("exited")
def gef_on_exit_unhook(func: Callable[["gdb.ExitedEvent"], None]) -> None:
    gdb.events.exited.disconnect(func)


@only_if_events_supported("new_objfile")
def gef_on_new_hook(func: Callable[["gdb.NewObjFileEvent"], None]) -> None:
    gdb.events.new_objfile.connect(func)


@only_if_events_supported("new_objfile")
def gef_on_new_unhook(func: Callable[["gdb.NewObjFileEvent"], None]) -> None:
    gdb.events.new_objfile.disconnect(func)


@only_if_events_supported("clear_objfiles")
def gef_on_unload_objfile_hook(func: Callable[["gdb.ClearObjFilesEvent"], None]) -> None:
    gdb.events.clear_objfiles.connect(func)


@only_if_events_supported("clear_objfiles")
def gef_on_unload_objfile_unhook(func: Callable[["gdb.ClearObjFilesEvent"], None]) -> None:
    gdb.events.clear_objfiles.disconnect(func)


@only_if_events_supported("memory_changed")
def gef_on_memchanged_hook(func: Callable[["gdb.MemoryChangedEvent"], None]) -> None:
    gdb.events.memory_changed.connect(func)


@only_if_events_supported("memory_changed")
def gef_on_memchanged_unhook(func: Callable[["gdb.MemoryChangedEvent"], None]) -> None:
    gdb.events.memory_changed.disconnect(func)


@only_if_events_supported("register_changed")
def gef_on_regchanged_hook(func: Callable[["gdb.RegisterChangedEvent"], None]) -> None:
    gdb.events.register_changed.connect(func)


@only_if_events_supported("register_changed")
def gef_on_regchanged_unhook(func: Callable[["gdb.RegisterChangedEvent"], None]) -> None:
    gdb.events.register_changed.disconnect(func)


#
# Breakpoints
#

class StubBreakpoint(gdb.Breakpoint):
    """Create a breakpoint to permanently disable a call (fork/alarm/signal/etc.)."""

    def __init__(self, func: str, retval: Optional[int]) -> None:
        super().__init__(func, gdb.BP_BREAKPOINT, internal=False)
        self.func = func
        self.retval = retval

        m = f"All calls to '{self.func}' will be skipped"
        if self.retval is not None:
            m += f" (with return value set to {self.retval:#x})"
        info(m)
        return

    def stop(self) -> bool:
        gdb.execute(f"return (unsigned int){self.retval:#x}")
        ok(f"Ignoring call to '{self.func}' "
           f"(setting return value to {self.retval:#x})")
        return False


class ChangePermissionBreakpoint(gdb.Breakpoint):
    """When hit, this temporary breakpoint will restore the original code, and position
    $pc correctly."""

    def __init__(self, loc: str, code: ByteString, pc: int) -> None:
        super().__init__(loc, gdb.BP_BREAKPOINT, internal=False)
        self.original_code = code
        self.original_pc = pc
        return

    def stop(self) -> bool:
        info("Restoring original context")
        gef.memory.write(self.original_pc, self.original_code, len(self.original_code))
        info("Restoring $pc")
        gdb.execute(f"set $pc = {self.original_pc:#x}")
        return True


class EntryBreakBreakpoint(gdb.Breakpoint):
    """Breakpoint used internally to stop execution at the most convenient entry point."""

    def __init__(self, location: str) -> None:
        super().__init__(location, gdb.BP_BREAKPOINT, internal=True, temporary=True)
        self.silent = True
        return

    def stop(self) -> bool:
        reset_all_caches()
        return True


class NamedBreakpoint(gdb.Breakpoint):
    """Breakpoint which shows a specified name, when hit."""

    def __init__(self, location: str, name: str) -> None:
        super().__init__(spec=location, type=gdb.BP_BREAKPOINT, internal=False, temporary=False)
        self.name = name
        self.loc = location
        return

    def stop(self) -> bool:
        reset_all_caches()
        push_context_message("info", f"Hit breakpoint {self.loc} ({Color.colorify(self.name, 'red bold')})")
        return True


#
# Context Panes
#

def register_external_context_pane(pane_name: str, display_pane_function: Callable[[], None], pane_title_function: Callable[[], Optional[str]], condition : Optional[Callable[[], bool]] = None) -> None:
    """
    Registering function for new GEF Context View.
    pane_name: a string that has no spaces (used in settings)
    display_pane_function: a function that uses gef_print() to print strings
    pane_title_function: a function that returns a string or None, which will be displayed as the title.
    If None, no title line is displayed.
    condition: an optional callback: if not None, the callback will be executed first. If it returns true,
      then only the pane title and content will displayed. Otherwise, it's simply skipped.

    Example usage for a simple text to show when we hit a syscall:
    def only_syscall(): return gef_current_instruction(gef.arch.pc).is_syscall()
    def display_pane():
      gef_print("Wow, I am a context pane!")
    def pane_title():
      return "example:pane"
    register_external_context_pane("example_pane", display_pane, pane_title, only_syscall)
    """
    gef.gdb.add_context_pane(pane_name, display_pane_function, pane_title_function, condition)
    return


#
# Commands
#
@deprecated("Use `register()`, and inherit from `GenericCommand` instead")
def register_external_command(cls: Type["GenericCommand"]) -> Type["GenericCommand"]:
    """Registering function for new GEF (sub-)command to GDB."""
    return cls

@deprecated("Use `register()`, and inherit from `GenericCommand` instead")
def register_command(cls: Type["GenericCommand"]) -> Type["GenericCommand"]:
    """Decorator for registering new GEF (sub-)command to GDB."""
    return cls

@deprecated("")
def register_priority_command(cls: Type["GenericCommand"]) -> Type["GenericCommand"]:
    """Decorator for registering new command with priority, meaning that it must
    loaded before the other generic commands."""
    return cls


def register(cls: Union[Type["GenericCommand"], Type["GenericFunction"]]) -> Union[Type["GenericCommand"], Type["GenericFunction"]]:
    global __registered_commands__, __registered_functions__
    if issubclass(cls, GenericCommand):
        assert( hasattr(cls, "_cmdline_"))
        assert( hasattr(cls, "do_invoke"))
        assert( all(map(lambda x: x._cmdline_ != cls._cmdline_, __registered_commands__)))
        __registered_commands__.add(cls)
        return cls

    if issubclass(cls, GenericFunction):
        assert( hasattr(cls, "_function_"))
        assert( hasattr(cls, "invoke"))
        assert( all(map(lambda x: x._function_ != cls._function_, __registered_functions__)))
        __registered_functions__.add(cls)
        return cls

    raise TypeError(f"`{cls.__class__}` is an illegal class for `register`")


class GenericCommand(gdb.Command):
    """This is an abstract class for invoking commands, should not be instantiated."""

    _cmdline_: str
    _syntax_: str
    _example_: Union[str, List[str]] = ""

    def __init_subclass__(cls, **kwargs):
        super().__init_subclass__(**kwargs)
        attributes = ("_cmdline_", "_syntax_", )
        if not all(map(lambda x: hasattr(cls, x), attributes)):
            raise NotImplementedError

    def __init__(self, *args: Any, **kwargs: Any) -> None:
        self.pre_load()
        syntax = Color.yellowify("\nSyntax: ") + self._syntax_
        example = Color.yellowify("\nExamples: \n\t")
        if isinstance(self._example_, list):
            example += "\n\t".join(self._example_)
        elif isinstance(self._example_, str):
            example += self._example_
        self.__doc__ = self.__doc__.replace(" "*4, "") + syntax + example
        self.repeat = False
        self.repeat_count = 0
        self.__last_command = None
        command_type = kwargs.setdefault("command", gdb.COMMAND_OBSCURE)
        complete_type = kwargs.setdefault("complete", gdb.COMPLETE_NONE)
        prefix = kwargs.setdefault("prefix", False)
        super().__init__(self._cmdline_, command_type, complete_type, prefix)
        self.post_load()
        return

    def invoke(self, args: str, from_tty: bool) -> None:
        try:
            argv = gdb.string_to_argv(args)
            self.__set_repeat_count(argv, from_tty)
            bufferize(self.do_invoke)(argv)
        except Exception as e:
            # Note: since we are intercepting cleaning exceptions here, commands preferably should avoid
            # catching generic Exception, but rather specific ones. This is allows a much cleaner use.
            if is_debug():
                show_last_exception()
            else:
                err(f"Command '{self._cmdline_}' failed to execute properly, reason: {e}")
        return

    def usage(self) -> None:
        err(f"Syntax\n{self._syntax_}")
        return

    def do_invoke(self, argv: List[str]) -> None:
        raise NotImplementedError

    def pre_load(self) -> None:
        return

    def post_load(self) -> None:
        return

    def __get_setting_name(self, name: str) -> str:
        clsname = self.__class__._cmdline_.replace(" ", "-")
        return f"{clsname}.{name}"

    def __iter__(self) -> Generator[str, None, None]:
        for key in gef.config.keys():
            if key.startswith(self._cmdline_):
                yield key.replace(f"{self._cmdline_}.", "", 1)

    @property
    def settings(self) -> List[str]:
        """Return the list of settings for this command."""
        return list(iter(self))

    @deprecated(f"Use `self[setting_name]` instead")
    def get_setting(self, name: str) -> Any:
        return self.__getitem__(name)

    def __getitem__(self, name: str) -> Any:
        key = self.__get_setting_name(name)
        return gef.config[key]

    @deprecated(f"Use `setting_name in self` instead")
    def has_setting(self, name: str) -> bool:
        return self.__contains__(name)

    def __contains__(self, name: str) -> bool:
        return self.__get_setting_name(name) in gef.config

    @deprecated(f"Use `self[setting_name] = value` instead")
    def add_setting(self, name: str, value: Tuple[Any, type, str], description: str = "") -> None:
        return self.__setitem__(name, (value, type(value), description))

    def __setitem__(self, name: str, value: Union[Any, Tuple[Any, str]]) -> None:
        # make sure settings are always associated to the root command (which derives from GenericCommand)
        if "GenericCommand" not in [x.__name__ for x in self.__class__.__bases__]:
            return
        key = self.__get_setting_name(name)
        if key in gef.config:
            setting = gef.config.raw_entry(key)
            setting.value = value
        else:
            if len(value) == 1:
                gef.config[key] = GefSetting(value[0])
            elif len(value) == 2:
                gef.config[key] = GefSetting(value[0], description=value[1])
        return

    @deprecated(f"Use `del self[setting_name]` instead")
    def del_setting(self, name: str) -> None:
        return self.__delitem__(name)

    def __delitem__(self, name: str) -> None:
        del gef.config[self.__get_setting_name(name)]
        return

    def __set_repeat_count(self, argv: List[str], from_tty: bool) -> None:
        if not from_tty:
            self.repeat = False
            self.repeat_count = 0
            return

        command = gdb.execute("show commands", to_string=True).strip().split("\n")[-1]
        self.repeat = self.__last_command == command
        self.repeat_count = self.repeat_count + 1 if self.repeat else 0
        self.__last_command = command
        return


@register
class VersionCommand(GenericCommand):
    """Display GEF version info."""

    _cmdline_ = "version"
    _syntax_ = f"{_cmdline_}"
    _example_ = f"{_cmdline_}"

    def do_invoke(self, argv: List[str]) -> None:
        gef_fpath = pathlib.Path(inspect.stack()[0][1]).expanduser().absolute()
        gef_dir = gef_fpath.parent
        with gef_fpath.open("rb") as f:
            gef_hash = hashlib.sha256(f.read()).hexdigest()

        if os.access(f"{gef_dir}/.git", os.X_OK):
            ver = subprocess.check_output("git log --format='%H' -n 1 HEAD", cwd=gef_dir, shell=True).decode("utf8").strip()
            extra = "dirty" if len(subprocess.check_output("git ls-files -m", cwd=gef_dir, shell=True).decode("utf8").strip()) else "clean"
            gef_print(f"GEF: rev:{ver} (Git - {extra})")
        else:
            gef_blob_hash = subprocess.check_output(f"git hash-object {gef_fpath}", shell=True).decode().strip()
            gef_print("GEF: (Standalone)")
            gef_print(f"Blob Hash({gef_fpath}): {gef_blob_hash}")
        gef_print(f"SHA256({gef_fpath}): {gef_hash}")
        gef_print(f"GDB: {gdb.VERSION}")
        py_ver = f"{sys.version_info.major:d}.{sys.version_info.minor:d}"
        gef_print(f"GDB-Python: {py_ver}")

        if "full" in argv:
            gef_print(f"Loaded commands: {', '.join(gef.gdb.loaded_command_names)}")
        return


@register
class PrintFormatCommand(GenericCommand):
    """Print bytes format in commonly used formats, such as literals in high level languages."""

    valid_formats = ("py", "c", "js", "asm", "hex", "bytearray")
    valid_bitness = (8, 16, 32, 64)

    _cmdline_ = "print-format"
    _aliases_ = ["pf",]
    _syntax_  = (f"{_cmdline_} [--lang LANG] [--bitlen SIZE] [(--length,-l) LENGTH] [--clip] LOCATION"
                 f"\t--lang LANG specifies the output format for programming language (available: {valid_formats!s}, default 'py')."
                 f"\t--bitlen SIZE specifies size of bit (possible values: {valid_bitness!s}, default is 8)."
                 "\t--length LENGTH specifies length of array (default is 256)."
                 "\t--clip The output data will be copied to clipboard"
                 "\tLOCATION specifies where the address of bytes is stored.")
    _example_ = f"{_cmdline_} --lang py -l 16 $rsp"

    def __init__(self) -> None:
        super().__init__(complete=gdb.COMPLETE_LOCATION)
        self["max_size_preview"] = (10, "max size preview of bytes")
        return

    @property
    def format_matrix(self) -> Dict[int, Tuple[str, str, str]]:
        # `gef.arch.endianness` is a runtime property, should not be defined as a class property
        return {
            8:  (f"{gef.arch.endianness}B", "char", "db"),
            16: (f"{gef.arch.endianness}H", "short", "dw"),
            32: (f"{gef.arch.endianness}I", "int", "dd"),
            64: (f"{gef.arch.endianness}Q", "long long", "dq"),
        }

    @only_if_gdb_running
    @parse_arguments({"location": "$pc", }, {("--length", "-l"): 256, "--bitlen": 0, "--lang": "py", "--clip": True,})
    def do_invoke(self, _: List[str], **kwargs: Any) -> None:
        """Default value for print-format command."""
        args: argparse.Namespace = kwargs["arguments"]
        args.bitlen = args.bitlen or gef.arch.ptrsize * 2

        valid_bitlens = self.format_matrix.keys()
        if args.bitlen not in valid_bitlens:
            err(f"Size of bit must be in: {valid_bitlens!s}")
            return

        if args.lang not in self.valid_formats:
            err(f"Language must be in: {self.valid_formats!s}")
            return

        start_addr = parse_address(args.location)
        size = int(args.bitlen / 8)
        end_addr = start_addr + args.length * size
        fmt = self.format_matrix[args.bitlen][0]
        data = []

        if args.lang != "bytearray":
            for addr in range(start_addr, end_addr, size):
                value = struct.unpack(fmt, gef.memory.read(addr, size))[0]
                data += [value]
            sdata = ", ".join(map(hex, data))

        if args.lang == "bytearray":
            data = gef.memory.read(start_addr, args.length)
            preview = str(data[0:self["max_size_preview"]])
            out = f"Saved data {preview}... in '{gef_convenience(data)}'"
        elif args.lang == "py":
            out = f"buf = [{sdata}]"
        elif args.lang == "c":
            c_type = self.format_matrix[args.bitlen][1]
            out = f"unsigned {c_type} buf[{args.length}] = {{{sdata}}};"
        elif args.lang == "js":
            out = f"var buf = [{sdata}]"
        elif args.lang == "asm":
            asm_type = self.format_matrix[args.bitlen][2]
            out = "buf {0} {1}".format(asm_type, sdata)
        elif args.lang == "hex":
            out = binascii.hexlify(gef.memory.read(start_addr, end_addr-start_addr)).decode()
        else:
            raise ValueError(f"Invalid format: {args.lang}")

        if args.clip:
            if copy_to_clipboard(gef_pybytes(out)):
                info("Copied to clipboard")
            else:
                warn("There's a problem while copying")

        gef_print(out)
        return


@register
class SmartEvalCommand(GenericCommand):
    """SmartEval: Smart eval (vague approach to mimic WinDBG `?`)."""

    _cmdline_ = "$"
    _syntax_  = f"{_cmdline_} EXPR\n{_cmdline_} ADDRESS1 ADDRESS2"
    _example_ = (f"\n{_cmdline_} $pc+1"
                 f"\n{_cmdline_} 0x00007ffff7a10000 0x00007ffff7bce000")

    def do_invoke(self, argv: List[str]) -> None:
        argc = len(argv)
        if argc == 1:
            self.evaluate(argv)
            return

        if argc == 2:
            self.distance(argv)
        return

    def evaluate(self, expr: List[str]) -> None:
        def show_as_int(i: int) -> None:
            off = gef.arch.ptrsize*8
            def comp2_x(x: Any) -> str: return f"{(x + (1 << off)) % (1 << off):x}"
            def comp2_b(x: Any) -> str: return f"{(x + (1 << off)) % (1 << off):b}"

            try:
                s_i = comp2_x(res)
                s_i = s_i.rjust(len(s_i)+1, "0") if len(s_i)%2 else s_i
                gef_print(f"{i:d}")
                gef_print("0x" + comp2_x(res))
                gef_print("0b" + comp2_b(res))
                gef_print(f"{binascii.unhexlify(s_i)}")
                gef_print(f"{binascii.unhexlify(s_i)[::-1]}")
            except:
                pass
            return

        parsed_expr = []
        for xp in expr:
            try:
                xp = gdb.parse_and_eval(xp)
                xp = int(xp)
                parsed_expr.append(f"{xp:d}")
            except gdb.error:
                parsed_expr.append(str(xp))

        try:
            res = eval(" ".join(parsed_expr))
            if isinstance(res, int):
                show_as_int(res)
            else:
                gef_print(f"{res}")
        except SyntaxError:
            gef_print(" ".join(parsed_expr))
        return

    def distance(self, args: Tuple[str, str]) -> None:
        try:
            x = int(args[0], 16) if is_hex(args[0]) else int(args[0])
            y = int(args[1], 16) if is_hex(args[1]) else int(args[1])
            gef_print(f"{abs(x - y)}")
        except ValueError:
            warn(f"Distance requires 2 numbers: {self._cmdline_} 0 0xffff")
        return


@register
class ProcessStatusCommand(GenericCommand):
    """Extends the info given by GDB `info proc`, by giving an exhaustive description of the
    process status (file descriptors, ancestor, descendants, etc.)."""

    _cmdline_ = "process-status"
    _syntax_  = _cmdline_
    _aliases_ = ["status", ]

    def __init__(self) -> None:
        super().__init__(complete=gdb.COMPLETE_NONE)
        return

    @only_if_gdb_running
    @only_if_gdb_target_local
    def do_invoke(self, argv: List[str]) -> None:
        self.show_info_proc()
        self.show_ancestor()
        self.show_descendants()
        self.show_fds()
        self.show_connections()
        return

    def get_state_of(self, pid: int) -> Dict[str, str]:
        res = {}
        with open(f"/proc/{pid}/status", "r") as f:
            file = f.readlines()
        for line in file:
            key, value = line.split(":", 1)
            res[key.strip()] = value.strip()
        return res

    def get_cmdline_of(self, pid: int) -> str:
        with open(f"/proc/{pid}/cmdline", "r") as f:
            return f.read().replace("\x00", "\x20").strip()

    def get_process_path_of(self, pid: int) -> str:
        return os.readlink(f"/proc/{pid}/exe")

    def get_children_pids(self, pid: int) -> List[int]:
        cmd = [gef.session.constants["ps"], "-o", "pid", "--ppid", f"{pid}", "--noheaders"]
        try:
            return [int(x) for x in gef_execute_external(cmd, as_list=True)]
        except Exception:
            return []

    def show_info_proc(self) -> None:
        info("Process Information")
        pid = gef.session.pid
        cmdline = self.get_cmdline_of(pid)
        gef_print(f"\tPID {RIGHT_ARROW} {pid}",
                  f"\tExecutable {RIGHT_ARROW} {self.get_process_path_of(pid)}",
                  f"\tCommand line {RIGHT_ARROW} '{cmdline}'", sep="\n")
        return

    def show_ancestor(self) -> None:
        info("Parent Process Information")
        ppid = int(self.get_state_of(gef.session.pid)["PPid"])
        state = self.get_state_of(ppid)
        cmdline = self.get_cmdline_of(ppid)
        gef_print(f"\tParent PID {RIGHT_ARROW} {state['Pid']}",
                  f"\tCommand line {RIGHT_ARROW} '{cmdline}'", sep="\n")
        return

    def show_descendants(self) -> None:
        info("Children Process Information")
        children = self.get_children_pids(gef.session.pid)
        if not children:
            gef_print("\tNo child process")
            return

        for child_pid in children:
            state = self.get_state_of(child_pid)
            pid = state["Pid"]
            gef_print(f"\tPID {RIGHT_ARROW} {pid} (Name: '{self.get_process_path_of(pid)}', CmdLine: '{self.get_cmdline_of(pid)}')")
            return

    def show_fds(self) -> None:
        pid = gef.session.pid
        path = f"/proc/{pid:d}/fd"

        info("File Descriptors:")
        items = os.listdir(path)
        if not items:
            gef_print("\tNo FD opened")
            return

        for fname in items:
            fullpath = os.path.join(path, fname)
            if os.path.islink(fullpath):
                gef_print(f"\t{fullpath} {RIGHT_ARROW} {os.readlink(fullpath)}")
        return

    def list_sockets(self, pid: int) -> List[int]:
        sockets = []
        path = f"/proc/{pid:d}/fd"
        items = os.listdir(path)
        for fname in items:
            fullpath = os.path.join(path, fname)
            if os.path.islink(fullpath) and os.readlink(fullpath).startswith("socket:"):
                p = os.readlink(fullpath).replace("socket:", "")[1:-1]
                sockets.append(int(p))
        return sockets

    def parse_ip_port(self, addr: str) -> Tuple[str, int]:
        ip, port = addr.split(":")
        return socket.inet_ntoa(struct.pack("<I", int(ip, 16))), int(port, 16)

    def show_connections(self) -> None:
        # https://github.com/torvalds/linux/blob/v4.7/include/net/tcp_states.h#L16
        tcp_states_str = {
            0x01: "TCP_ESTABLISHED",
            0x02: "TCP_SYN_SENT",
            0x03: "TCP_SYN_RECV",
            0x04: "TCP_FIN_WAIT1",
            0x05: "TCP_FIN_WAIT2",
            0x06: "TCP_TIME_WAIT",
            0x07: "TCP_CLOSE",
            0x08: "TCP_CLOSE_WAIT",
            0x09: "TCP_LAST_ACK",
            0x0A: "TCP_LISTEN",
            0x0B: "TCP_CLOSING",
            0x0C: "TCP_NEW_SYN_RECV",
        }

        udp_states_str = {
            0x07: "UDP_LISTEN",
        }

        info("Network Connections")
        pid = gef.session.pid
        sockets = self.list_sockets(pid)
        if not sockets:
            gef_print("\tNo open connections")
            return

        entries = dict()
        with open(f"/proc/{pid:d}/net/tcp", "r") as tcp:
            entries["TCP"] = [x.split() for x in tcp.readlines()[1:]]
        with open(f"/proc/{pid:d}/net/udp", "r") as udp:
            entries["UDP"] = [x.split() for x in udp.readlines()[1:]]

        for proto in entries:
            for entry in entries[proto]:
                local, remote, state = entry[1:4]
                inode = int(entry[9])
                if inode in sockets:
                    local = self.parse_ip_port(local)
                    remote = self.parse_ip_port(remote)
                    state = int(state, 16)
                    state_str = tcp_states_str[state] if proto == "TCP" else udp_states_str[state]

                    gef_print(f"\t{local[0]}:{local[1]} {RIGHT_ARROW} {remote[0]}:{remote[1]} ({state_str})")
        return


@register
class GefThemeCommand(GenericCommand):
    """Customize GEF appearance."""

    _cmdline_ = "theme"
    _syntax_ = f"{_cmdline_} [KEY [VALUE]]"

    def __init__(self) -> None:
        super().__init__(self._cmdline_)
        self["context_title_line"] = ("gray", "Color of the borders in context window")
        self["context_title_message"] = ("cyan", "Color of the title in context window")
        self["default_title_line"] = ("gray", "Default color of borders")
        self["default_title_message"] = ("cyan", "Default color of title")
        self["table_heading"] = ("blue", "Color of the column headings to tables (e.g. vmmap)")
        self["old_context"] = ("gray", "Color to use to show things such as code that is not immediately relevant")
        self["disassemble_current_instruction"] = ("green", "Color to use to highlight the current $pc when disassembling")
        self["dereference_string"] = ("yellow", "Color of dereferenced string")
        self["dereference_code"] = ("gray", "Color of dereferenced code")
        self["dereference_base_address"] = ("cyan", "Color of dereferenced address")
        self["dereference_register_value"] = ("bold blue", "Color of dereferenced register")
        self["registers_register_name"] = ("blue", "Color of the register name in the register window")
        self["registers_value_changed"] = ("bold red", "Color of the changed register in the register window")
        self["address_iwram"] = ("pink", "Color to use when a IWRAM address is found")
        self["address_ewram"] = ("green", "Color to use when a EWRAM address is found")
        self["address_rom0"] = ("red", "Color to use when a code address is found")
        self["source_current_line"] = ("green", "Color to use for the current code line in the source window")
        return

    def do_invoke(self, args: List[str]) -> None:
        self.dont_repeat()
        argc = len(args)

        if argc == 0:
            for key in self.settings:
                setting = self[key]
                value = Color.colorify(setting, setting)
                gef_print(f"{key:40s}: {value}")
            return

        setting_name = args[0]
        if not setting_name in self:
            err("Invalid key")
            return

        if argc == 1:
            value = self[setting_name]
            gef_print(f"{setting_name:40s}: {Color.colorify(value, value)}")
            return

        colors = [color for color in args[1:] if color in Color.colors]
        self[setting_name] = " ".join(colors)
        return


class ExternalStructureManager:
    class Structure:
        def __init__(self, manager: "ExternalStructureManager", mod_path: pathlib.Path, struct_name: str) -> None:
            self.manager = manager
            self.module_path = mod_path
            self.name = struct_name
            self.class_type = self.__get_structure_class()
            # if the symbol points to a class factory method and not a class
            if not hasattr(self.class_type, "_fields_") and callable(self.class_type):
                self.class_type = self.class_type(gef)
            return

        def __str__(self) -> str:
            return self.name

        def pprint(self) -> None:
            res = []
            for _name, _type in self.class_type._fields_:
                size = ctypes.sizeof(_type)
                name = Color.colorify(_name, gef.config["pcustom.structure_name"])
                type = Color.colorify(_type.__name__, gef.config["pcustom.structure_type"])
                size = Color.colorify(hex(size), gef.config["pcustom.structure_size"])
                offset = Color.boldify(f"{getattr(self.class_type, _name).offset:04x}")
                res.append(f"{offset}   {name:32s}   {type:16s}  /* size={size} */")
            gef_print("\n".join(res))
            return

        def __get_structure_class(self) -> Type:
            """Returns a tuple of (class, instance) if modname!classname exists"""
            fpath = self.module_path
            spec = importlib.util.spec_from_file_location(fpath.stem, fpath)
            module = importlib.util.module_from_spec(spec)
            sys.modules[fpath.stem] = module
            spec.loader.exec_module(module)
            _class = getattr(module, self.name)
            return _class

        def apply_at(self, address: int, max_depth: int, depth: int = 0) -> None:
            """Apply (recursively if possible) the structure format to the given address."""
            if depth >= max_depth:
                warn("maximum recursion level reached")
                return

            # read the data at the specified address
            _structure = self.class_type()
            _sizeof_structure = ctypes.sizeof(_structure)

            try:
                data = gef.memory.read(address, _sizeof_structure)
            except gdb.MemoryError:
                err(f"{' ' * depth}Cannot read memory {address:#x}")
                return

            # deserialize the data
            length = min(len(data), _sizeof_structure)
            ctypes.memmove(ctypes.addressof(_structure), data, length)

            # pretty print all the fields (and call recursively if possible)
            ptrsize = gef.arch.ptrsize
            unpack = u32 if ptrsize == 4 else u64
            for field in _structure._fields_:
                _name, _type = field
                _value = getattr(_structure, _name)
                _offset = getattr(self.class_type, _name).offset

                if ((ptrsize == 4 and _type is ctypes.c_uint32)
                    or (ptrsize == 8 and _type is ctypes.c_uint64)
                    or (ptrsize == ctypes.sizeof(ctypes.c_void_p) and _type is ctypes.c_void_p)):
                    # try to dereference pointers
                    _value = RIGHT_ARROW.join(dereference_from(_value))

                line = f"{'  ' * depth}"
                line += f"{address:#x}+{_offset:#04x} {_name} : ".ljust(40)
                line += f"{_value} ({_type.__name__})"
                parsed_value = self.__get_ctypes_value(_structure, _name, _value)
                if parsed_value:
                    line += f"{RIGHT_ARROW} {parsed_value}"
                gef_print(line)

                if issubclass(_type, ctypes.Structure):
                    self.apply_at(address + _offset, max_depth, depth + 1)
                elif _type.__name__.startswith("LP_"):
                    # Pointer to a structure of a different type
                    __sub_type_name = _type.__name__.lstrip("LP_")
                    result = self.manager.find(__sub_type_name)
                    if result:
                        _, __structure = result
                        __address = unpack(gef.memory.read(address + _offset, ptrsize))
                        __structure.apply_at(__address, max_depth, depth + 1)
            return

        def __get_ctypes_value(self, struct, item, value) -> str:
            if not hasattr(struct, "_values_"): return ""
            default = ""
            for name, values in struct._values_:
                if name != item: continue
                if callable(values):
                    return values(value)
                try:
                    for val, desc in values:
                        if value == val: return desc
                        if val is None: default = desc
                except Exception as e:
                    err(f"Error parsing '{name}': {e}")
            return default

    class Module(dict):
        def __init__(self, manager: "ExternalStructureManager", path: pathlib.Path) -> None:
            self.manager = manager
            self.path = path
            self.name = path.stem
            self.raw = self.__load()

            for entry in self:
                structure = ExternalStructureManager.Structure(manager, self.path, entry)
                self[structure.name] = structure
            return

        def __load(self) -> ModuleType:
            """Load a custom module, and return it."""
            fpath = self.path
            spec = importlib.util.spec_from_file_location(fpath.stem, fpath)
            module = importlib.util.module_from_spec(spec)
            sys.modules[fpath.stem] = module
            spec.loader.exec_module(module)
            return module

        def __str__(self) -> str:
            return self.name

        def __iter__(self) -> Generator[str, None, None]:
            _invalid = {"BigEndianStructure", "LittleEndianStructure", "Structure"}
            for x in dir(self.raw):
                if x in _invalid: continue
                _attr = getattr(self.raw, x)

                # if it's a ctypes.Structure class, add it
                if inspect.isclass(_attr) and issubclass(_attr, ctypes.Structure):
                    yield x
                    continue

                # also accept class factory functions
                if callable(_attr) and _attr.__module__ == self.name and x.endswith("_t"):
                    yield x
                    continue
            return

    class Modules(dict):
        def __init__(self, manager: "ExternalStructureManager") -> None:
            self.manager: "ExternalStructureManager" = manager
            self.root: pathlib.Path = manager.path

            for entry in self.root.iterdir():
                if not entry.is_file(): continue
                if entry.suffix != ".py": continue
                if entry.name == "__init__.py": continue
                module = ExternalStructureManager.Module(manager, entry)
                self[module.name] = module
            return

        def __contains__(self, structure_name: str) -> bool:
            """Return True if the structure name is found in any of the modules"""
            for module in self.values():
                if structure_name in module:
                    return True
            return False

    def __init__(self) -> None:
        self.clear_caches()
        return

    def clear_caches(self) -> None:
        self._path = None
        self._modules = None
        return

    @property
    def modules(self) -> "ExternalStructureManager.Modules":
        if not self._modules:
            self._modules = ExternalStructureManager.Modules(self)
        return self._modules

    @property
    def path(self) -> pathlib.Path:
        if not self._path:
            self._path = pathlib.Path(gef.config["pcustom.struct_path"]).expanduser().absolute()
        return self._path

    @property
    def structures(self) -> Generator[Tuple["ExternalStructureManager.Module", "ExternalStructureManager.Structure"], None, None]:
        for module in self.modules.values():
            for structure in module.values():
                yield module, structure
        return

    @lru_cache()
    def find(self, structure_name: str) -> Optional[Tuple["ExternalStructureManager.Module", "ExternalStructureManager.Structure"]]:
        """Return the module and structure for the given structure name; `None` if the structure name was not found."""
        for module in self.modules.values():
            if structure_name in module:
                return module, module[structure_name]
        return None


@register
class PCustomCommand(GenericCommand):
    """Dump user defined structure.
    This command attempts to reproduce WinDBG awesome `dt` command for GDB and allows
    to apply structures (from symbols or custom) directly to an address.
    Custom structures can be defined in pure Python using ctypes, and should be stored
    in a specific directory, whose path must be stored in the `pcustom.struct_path`
    configuration setting."""

    _cmdline_ = "pcustom"
    _syntax_  = f"{_cmdline_} [list|edit <StructureName>|show <StructureName>]|<StructureName> 0xADDRESS]"

    def __init__(self) -> None:
        super().__init__(prefix=True)
        self["struct_path"] = (str(pathlib.Path(gef.config["gef.tempdir"]) / "structs"), "Path to store/load the structure ctypes files")
        self["max_depth"] = (4, "Maximum level of recursion supported")
        self["structure_name"] = ("bold blue", "Color of the structure name")
        self["structure_type"] = ("bold red", "Color of the attribute type")
        self["structure_size"] = ("green", "Color of the attribute size")
        return

    @parse_arguments({"type": "", "address": ""}, {})
    def do_invoke(self, *_: Any, **kwargs: Dict[str, Any]) -> None:
        args = kwargs["arguments"]
        if not args.type:
            gdb.execute("pcustom list")
            return

        _, structname = self.explode_type(args.type)

        if not args.address:
            gdb.execute(f"pcustom show {structname}")
            return

        if not is_alive():
            err("Session is not active")
            return

        manager = ExternalStructureManager()
        address = parse_address(args.address)
        result = manager.find(structname)
        if not result:
            err(f"No structure named '{structname}' found")
            return

        _, structure = result
        structure.apply_at(address, self["max_depth"])
        return

    def explode_type(self, arg: str) -> Tuple[str, str]:
        modname, structname = arg.split(":", 1) if ":" in arg else (arg, arg)
        structname = structname.split(".", 1)[0] if "." in structname else structname
        return modname, structname


@register
class PCustomListCommand(PCustomCommand):
    """PCustom: list available structures"""

    _cmdline_ = "pcustom list"
    _syntax_ = f"{_cmdline_}"

    def __init__(self) -> None:
        super().__init__()
        return

    def do_invoke(self, _: List) -> None:
        """Dump the list of all the structures and their respective."""
        manager = ExternalStructureManager()
        info(f"Listing custom structures from '{manager.path}'")
        struct_color = gef.config["pcustom.structure_type"]
        filename_color = gef.config["pcustom.structure_name"]
        for module in manager.modules.values():
            __modules = ", ".join([Color.colorify(structure_name, struct_color) for structure_name in module.values()])
            __filename = Color.colorify(str(module.path), filename_color)
            gef_print(f"{RIGHT_ARROW} {__filename} ({__modules})")
        return


@register
class PCustomShowCommand(PCustomCommand):
    """PCustom: show the content of a given structure"""

    _cmdline_ = "pcustom show"
    _syntax_ = f"{_cmdline_} StructureName"
    __aliases__ = ["pcustom create", "pcustom update"]

    def __init__(self) -> None:
        super().__init__()
        return

    def do_invoke(self, argv: List[str]) -> None:
        if len(argv) == 0:
            self.usage()
            return

        _, structname = self.explode_type(argv[0])
        manager = ExternalStructureManager()
        result = manager.find(structname)
        if result:
            _, structure = result
            structure.pprint()
        else:
            err(f"No structure named '{structname}' found")
        return


@register
class PCustomEditCommand(PCustomCommand):
    """PCustom: edit the content of a given structure"""

    _cmdline_ = "pcustom edit"
    _syntax_ = f"{_cmdline_} StructureName"
    __aliases__ = ["pcustom create", "pcustom new", "pcustom update"]

    def __init__(self) -> None:
        super().__init__()
        return

    def do_invoke(self, argv: List[str]) -> None:
        if len(argv) == 0:
            self.usage()
            return

        modname, structname = self.explode_type(argv[0])
        self.__create_or_edit_structure(modname, structname)
        return

    def __create_or_edit_structure(self, mod_name: str, struct_name: str) -> int:
        path = pathlib.Path(gef.config["pcustom.struct_path"]).expanduser() / f"{mod_name}.py"
        if path.is_file():
            info(f"Editing '{path}'")
        else:
            ok(f"Creating '{path}' from template")
            self.__create_template(struct_name, path)

        cmd = (os.getenv("EDITOR") or "nano").split()
        cmd.append(str(path.absolute()))
        return subprocess.call(cmd)

    def __create_template(self, structname: str, fpath: pathlib.Path) -> None:
        template = f"""from ctypes import *

class {structname}(Structure):
    _fields_ = []

    _values_ = []
"""
        with fpath.open("w") as f:
            f.write(template)
        return


@register
class ChangeFdCommand(GenericCommand):
    """ChangeFdCommand: redirect file descriptor during runtime."""

    _cmdline_ = "hijack-fd"
    _syntax_ = f"{_cmdline_} FD_NUM NEW_OUTPUT"
    _example_ = f"{_cmdline_} 2 /tmp/stderr_output.txt"

    @only_if_gdb_running
    @only_if_gdb_target_local
    def do_invoke(self, argv: List[str]) -> None:
        if len(argv) != 2:
            self.usage()
            return

        if not os.access(f"/proc/{gef.session.pid:d}/fd/{argv[0]}", os.R_OK):
            self.usage()
            return

        old_fd = int(argv[0])
        new_output = argv[1]

        if ":" in new_output:
            address = socket.gethostbyname(new_output.split(":")[0])
            port = int(new_output.split(":")[1])

            AF_INET = 2
            SOCK_STREAM = 1
            res = gdb.execute(f"""call (int)socket({AF_INET}, {SOCK_STREAM}, 0)""", to_string=True)
            new_fd = self.get_fd_from_result(res)

            # fill in memory with sockaddr_in struct contents
            # we will do this in the stack, since connect() wants a pointer to a struct
            vmmap = gef.memory.maps
            stack_addr = [entry.start for entry in vmmap if entry.path == "[stack]"][0]
            original_contents = gef.memory.read(stack_addr, 8)

            gef.memory.write(stack_addr, b"\x02\x00", 2)
            gef.memory.write(stack_addr + 0x2, struct.pack("<H", socket.htons(port)), 2)
            gef.memory.write(stack_addr + 0x4, socket.inet_aton(address), 4)

            info(f"Trying to connect to {new_output}")
            res = gdb.execute(f"""call (int)connect({new_fd}, {stack_addr}, {16})""", to_string=True)

            # recover stack state
            gef.memory.write(stack_addr, original_contents, 8)

            res = self.get_fd_from_result(res)
            if res == -1:
                err(f"Failed to connect to {address}:{port}")
                return

            info(f"Connected to {new_output}")
        else:
            res = gdb.execute(f"""call (int)open("{new_output}", 66, 0666)""", to_string=True)
            new_fd = self.get_fd_from_result(res)

        info(f"Opened '{new_output}' as fd #{new_fd:d}")
        gdb.execute(f"""call (int)dup2({new_fd:d}, {old_fd:d})""", to_string=True)
        info(f"Duplicated fd #{new_fd:d}{RIGHT_ARROW}#{old_fd:d}")
        gdb.execute(f"""call (int)close({new_fd:d})""", to_string=True)
        info(f"Closed extra fd #{new_fd:d}")
        ok("Success")
        return

    def get_fd_from_result(self, res: str) -> int:
        # Output example: $1 = 3
        res = gdb.execute(f"""p/d {int(res.split()[2], 0)}""", to_string=True)
        return int(res.split()[2], 0)


@register
class ScanSectionCommand(GenericCommand):
    """Search for addresses that are located in a memory mapping (haystack) that belonging
    to another (needle)."""

    _cmdline_ = "scan"
    _syntax_  = f"{_cmdline_} HAYSTACK NEEDLE"
    _aliases_ = ["lookup",]
    _example_ = f"\n{_cmdline_} stack"

    @only_if_gdb_running
    def do_invoke(self, argv: List[str]) -> None:
        if len(argv) != 2:
            self.usage()
            return

        haystack = argv[0]
        needle = argv[1]

        info(f"Searching for addresses in '{Color.yellowify(haystack)}' "
             f"that point to '{Color.yellowify(needle)}'")

        if haystack == "binary":
            haystack = get_filepath()

        if needle == "binary":
            needle = get_filepath()

        needle_sections = []
        haystack_sections = []

        if "0x" in haystack:
            start, end = parse_string_range(haystack)
            haystack_sections.append((start, end, ""))

        if "0x" in needle:
            start, end = parse_string_range(needle)
            needle_sections.append((start, end))

        for sect in gef.memory.maps:
            if haystack in sect.name:
                haystack_sections.append((sect.start, sect.end, os.path.basename(sect.name)))
            if needle in sect.name:
                needle_sections.append((sect.start, sect.end))

        step = gef.arch.ptrsize
        unpack = u32 if step == 4 else u64

        for hstart, hend, hname in haystack_sections:
            try:
                mem = gef.memory.read(hstart, hend - hstart)
            except gdb.MemoryError:
                continue

            for i in range(0, len(mem), step):
                target = unpack(mem[i:i+step])
                for nstart, nend in needle_sections:
                    if target >= nstart and target < nend:
                        deref = DereferenceCommand.pprint_dereferenced(hstart, int(i / step))
                        if hname != "":
                            name = Color.colorify(hname, "yellow")
                            gef_print(f"{name}: {deref}")
                        else:
                            gef_print(f" {deref}")

        return


@register
class SearchPatternCommand(GenericCommand):
    """SearchPatternCommand: search a pattern in memory. If given an hex value (starting with 0x)
    the command will also try to look for upwards cross-references to this address."""

    _cmdline_ = "search-pattern"
    _syntax_ = f"{_cmdline_} PATTERN [little|big] [section]"
    _aliases_ = ["grep", "xref"]
    _example_ = [f"{_cmdline_} AAAAAAAA",
                 f"{_cmdline_} 0x555555554000 little stack",
                 f"{_cmdline_} AAAA 0x600000-0x601000",
                 f"{_cmdline_} --regex 0x401000 0x401500 ([\\\\x20-\\\\x7E]{{2,}})(?=\\\\x00)   <-- It matchs null-end-printable(from x20-x7e) C strings (min size 2 bytes)"]

    def __init__(self) -> None:
        super().__init__()
        self["max_size_preview"] = (10, "max size preview of bytes")
        self["nr_pages_chunk"] = (0x400, "number of pages readed for each memory read chunk")
        return
        
    def print_section(self, section: Section) -> None:
        title = "In "
        if section.path:
            title += f"'{Color.blueify(section.path)}'"

        title += f"({section.start:#x}-{section.end:#x})"
        title += f", permission={section.permission}"
        ok(title)
        return

    def print_loc(self, loc: Tuple[int, int, str]) -> None:
        gef_print(f"""  {loc[0]:#x} - {loc[1]:#x} {RIGHT_ARROW}  "{Color.pinkify(loc[2])}" """)
        return

    def search_pattern_by_address(self, pattern: str, start_address: int, end_address: int) -> List[Tuple[int, int, Optional[str]]]:
        """Search a pattern within a range defined by arguments."""
        _pattern = gef_pybytes(pattern)
        step = self["nr_pages_chunk"] * gef.session.pagesize
        locations = []

        for chunk_addr in range(start_address, end_address, step):
            if chunk_addr + step > end_address:
                chunk_size = end_address - chunk_addr
            else:
                chunk_size = step

            try:
                mem = gef.memory.read(chunk_addr, chunk_size)
            except gdb.MemoryError as e:
                return []

            for match in re.finditer(_pattern, mem):
                start = chunk_addr + match.start()
                if is_ascii_string(start):
                    ustr = gef.memory.read_ascii_string(start) or ""
                    end = start + len(ustr)
                else:
                    ustr = gef_pystring(_pattern) + "[...]"
                    end = start + len(_pattern)
                locations.append((start, end, ustr))

            del mem

        return locations

    def search_binpattern_by_address(self, binpattern: bytes, start_address: int, end_address: int) -> List[Tuple[int, int, Optional[str]]]:
        """Search a binary pattern within a range defined by arguments."""

        step = self["nr_pages_chunk"] * gef.session.pagesize
        locations = []

        for chunk_addr in range(start_address, end_address, step):
            if chunk_addr + step > end_address:
                chunk_size = end_address - chunk_addr
            else:
                chunk_size = step

            try:
                mem = gef.memory.read(chunk_addr, chunk_size)
            except gdb.MemoryError as e:
                return []
            preview_size = self["max_size_preview"]
            for match in re.finditer(binpattern, mem):
                start = chunk_addr + match.start()
                preview = str(mem[slice(*match.span())][0:preview_size]) + "..."
                size_match = match.span()[1] - match.span()[0]
                if size_match > 0:
                    size_match -= 1
                end = start + size_match

                locations.append((start, end, preview))

            del mem

        return locations

    def search_pattern(self, pattern: str, section_name: str) -> None:
        """Search a pattern within the whole userland memory."""
        for section in gef.memory.maps:
            if not section.permission & Permission.READ: continue
            if section.path == "[vvar]": continue
            if not section_name in section.path: continue

            start = section.start
            end = section.end - 1
            old_section = None

            for loc in self.search_pattern_by_address(pattern, start, end):
                addr_loc_start = lookup_address(loc[0])
                if addr_loc_start and addr_loc_start.section:
                    if old_section != addr_loc_start.section:
                        self.print_section(addr_loc_start.section)
                        old_section = addr_loc_start.section

                self.print_loc(loc)
        return

    @only_if_gdb_running
    def do_invoke(self, argv: List[str]) -> None:
        argc = len(argv)
        if argc < 1:
            self.usage()
            return

        if argc > 3 and argv[0].startswith("--regex"):
            pattern = ' '.join(argv[3:])
            pattern = ast.literal_eval("b'" + pattern + "'")

            addr_start = parse_address(argv[1])
            addr_end = parse_address(argv[2])

            for loc in self.search_binpattern_by_address(pattern, addr_start, addr_end):
                self.print_loc(loc)

            return

        pattern = argv[0]
        endian = gef.arch.endianness

        if argc >= 2:
            if argv[1].lower() == "big": endian = Endianness.BIG_ENDIAN
            elif argv[1].lower() == "little": endian = Endianness.LITTLE_ENDIAN

        if is_hex(pattern):
            if endian == Endianness.BIG_ENDIAN:
                pattern = "".join(["\\x" + pattern[i:i + 2] for i in range(2, len(pattern), 2)])
            else:
                pattern = "".join(["\\x" + pattern[i:i + 2] for i in range(len(pattern) - 2, 0, -2)])

        if argc == 3:
            info(f"Searching '{Color.yellowify(pattern)}' in {argv[2]}")

            if "0x" in argv[2]:
                start, end = parse_string_range(argv[2])

                loc = lookup_address(start)
                if loc.valid:
                    self.print_section(loc.section)

                for loc in self.search_pattern_by_address(pattern, start, end):
                    self.print_loc(loc)
            else:
                section_name = argv[2]
                if section_name == "binary":
                    section_name = get_filepath() or ""

                self.search_pattern(pattern, section_name)
        else:
            info(f"Searching '{Color.yellowify(pattern)}' in memory")
            self.search_pattern(pattern, "")
        return


@register
class FlagsCommand(GenericCommand):
    """Edit flags in a human friendly way."""

    _cmdline_ = "edit-flags"
    _syntax_  = f"{_cmdline_} [(+|-|~)FLAGNAME ...]"
    _aliases_ = ["flags",]
    _example_ = (f"\n{_cmdline_}"
                 f"\n{_cmdline_} +zero # sets ZERO flag")

    def do_invoke(self, argv: List[str]) -> None:
        if not gef.arch.flag_register:
            warn(f"The architecture {gef.arch.arch}:{gef.arch.mode} doesn't have flag register.")
            return

        for flag in argv:
            if len(flag) < 2:
                continue

            action = flag[0]
            name = flag[1:].lower()

            if action not in ("+", "-", "~"):
                err(f"Invalid action for flag '{flag}'")
                continue

            if name not in gef.arch.flags_table.values():
                err(f"Invalid flag name '{flag[1:]}'")
                continue

            for off in gef.arch.flags_table:
                if gef.arch.flags_table[off] == name:
                    old_flag = gef.arch.register(gef.arch.flag_register)
                    if action == "+":
                        new_flags = old_flag | (1 << off)
                    elif action == "-":
                        new_flags = old_flag & ~(1 << off)
                    else:
                        new_flags = old_flag ^ (1 << off)

                    gdb.execute(f"set ({gef.arch.flag_register}) = {new_flags:#x}")

        gef_print(gef.arch.flag_register_to_human())
        return


@register
class RemoteCommand(GenericCommand):
    """GDB `target remote` command on steroids. This command will use the remote procfs to create
    a local copy of the execution environment, including the target binary and its libraries
    in the local temporary directory (the value by default is in `gef.config.tempdir`). Additionally, it
    will fetch all the /proc/PID/maps and loads all its information. If procfs is not available remotely, the command
    will likely fail. You can however still use the limited command provided by GDB `target remote`."""

    _cmdline_ = "gef-remote"
    _syntax_  = f"{_cmdline_} [OPTIONS] TARGET"
    _example_  = [f"{_cmdline_} localhost 1234",
                  f"{_cmdline_} --pid 6789 localhost 1234",
                  f"{_cmdline_} --qemu-user --qemu-binary /bin/debugme localhost 4444 "]

    def __init__(self) -> None:
        super().__init__(prefix=False)
        return

    @parse_arguments({"host": "", "port": 0}, {"--pid": -1, "--qemu-user": True, "--qemu-binary": ""})
    def do_invoke(self, _: List[str], **kwargs: Any) -> None:
        if gef.session.remote is not None:
            err("You already are in remote session. Close it first before opening a new one...")
            return

        # argument check
        args = kwargs["arguments"]
        if not args.host or not args.port:
            err("Missing parameters")
            return

        # qemu-user support
        qemu_binary: Optional[pathlib.Path] = None
        try:
            if args.qemu_user:
                qemu_binary = pathlib.Path(args.qemu_binary).expanduser().absolute() if args.qemu_binary else gef.session.file
                if not qemu_binary or not qemu_binary.exists():
                    raise FileNotFoundError(f"{qemu_binary} does not exist")
        except Exception as e:
            err(f"Failed to initialize qemu-user mode, reason: {str(e)}")
            return

        # try to establish the remote session, throw on error
        gef.session.remote = GefRemoteSessionManager(args.host, args.port, args.pid, qemu_binary)
        reset_all_caches()
        gdb.execute("context")
        return


@register
class NopCommand(GenericCommand):
    """Patch the instruction(s) pointed by parameters with NOP. Note: this command is architecture
    aware."""

    _cmdline_ = "nop"
    _syntax_  = ("{_cmdline_} [LOCATION] [--nb NUM_BYTES]"
                 "\n\tLOCATION\taddress/symbol to patch"
                 "\t--nb NUM_BYTES\tInstead of writing one instruction, patch the specified number of bytes")
    _example_ = f"{_cmdline_} $pc"

    def __init__(self) -> None:
        super().__init__(complete=gdb.COMPLETE_LOCATION)
        return

    @only_if_gdb_running
    @parse_arguments({"address": "$pc"}, {"--nb": 0, })
    def do_invoke(self, _: List[str], **kwargs: Any) -> None:
        args = kwargs["arguments"]
        address = parse_address(args.address)
        nop = gef.arch.nop_insn
        number_of_bytes = args.nb or 1
        insn = gef_get_instruction_at(address)

        if insn.size() != number_of_bytes:
            warn(f"Patching {number_of_bytes} bytes at {address:#x} might result in corruption")

        nops = bytearray(nop * number_of_bytes)
        end_address = Address(value=address + len(nops))
        if not end_address.valid:
            err(f"Cannot patch instruction at {address:#x}: reaching unmapped area")
            return

        ok(f"Patching {len(nops)} bytes from {address:#x}")
        gef.memory.write(address, nops, len(nops))
        return


@register
class StubCommand(GenericCommand):
    """Stub out the specified function. This function is useful when needing to skip one
    function to be called and disrupt your runtime flow (ex. fork)."""

    _cmdline_ = "stub"
    _syntax_  = (f"{_cmdline_} [--retval RETVAL] [address]"
                 "\taddress\taddress/symbol to stub out"
                 "\t--retval RETVAL\tSet the return value")
    _example_ = f"{_cmdline_} --retval 0 fork"

    def __init__(self) -> None:
        super().__init__(complete=gdb.COMPLETE_LOCATION)
        return

    @only_if_gdb_running
    @parse_arguments({"address": ""}, {("-r", "--retval"): 0})
    def do_invoke(self, _: List[str], **kwargs: Any) -> None:
        args = kwargs["arguments"]
        loc = args.address if args.address else f"*{gef.arch.pc:#x}"
        StubBreakpoint(loc, args.retval)
        return


@register
class DetailRegistersCommand(GenericCommand):
    """Display full details on one, many or all registers value from current architecture."""

    _cmdline_ = "registers"
    _syntax_  = f"{_cmdline_} [[Register1][Register2] ... [RegisterN]]"
    _example_ = (f"\n{_cmdline_}"
                 f"\n{_cmdline_} $r0 $sp $pc")

    @only_if_gdb_running
    @parse_arguments({"registers": [""]}, {})
    def do_invoke(self, _: List[str], **kwargs: Any) -> None:
        unchanged_color = gef.config["theme.registers_register_name"]
        changed_color = gef.config["theme.registers_value_changed"]
        string_color = gef.config["theme.dereference_string"]
        regs = gef.arch.all_registers

        args = kwargs["arguments"]
        if args.registers and args.registers[0]:
            required_regs = set(args.registers)
            valid_regs = [reg for reg in gef.arch.all_registers if reg in required_regs]
            if valid_regs:
                regs = valid_regs
            invalid_regs = [reg for reg in required_regs if reg not in valid_regs]
            if invalid_regs:
                err(f"invalid registers for architecture: {', '.join(invalid_regs)}")

        memsize = gef.arch.ptrsize
        endian = str(gef.arch.endianness)
        charset = string.printable
        widest = max(map(len, gef.arch.all_registers))
        special_line = ""

        for regname in regs:
            reg = gdb.parse_and_eval(regname)
            if reg.type.code == gdb.TYPE_CODE_VOID:
                continue

            padreg = regname.ljust(widest, " ")

            if str(reg) == "<unavailable>":
                gef_print(f"{Color.colorify(padreg, unchanged_color)}: "
                          f"{Color.colorify('no value', 'yellow underline')}")
                continue

            value = align_address(int(reg))
            old_value = ContextCommand.old_registers.get(regname, 0)
            if value == old_value:
                color = unchanged_color
            else:
                color = changed_color

            # Special (e.g. segment) registers go on their own line
            if regname in gef.arch.special_registers:
                special_line += f"{Color.colorify(regname, color)}: "
                special_line += f"{gef.arch.register(regname):#04x} "
                continue

            line = f"{Color.colorify(padreg, color)}: "

            if regname == gef.arch.flag_register:
                line += gef.arch.flag_register_to_human()
                gef_print(line)
                continue

            addr = lookup_address(align_address(int(value)))
            if addr.valid:
                line += str(addr)
            else:
                line += format_address_spaces(value)
            addrs = dereference_from(value)

            if len(addrs) > 1:
                sep = f" {RIGHT_ARROW} "
                line += sep
                line += sep.join(addrs[1:])

            # check to see if reg value is ascii
            try:
                fmt = f"{endian}{'I' if memsize == 4 else 'Q'}"
                last_addr = int(addrs[-1], 16)
                val = gef_pystring(struct.pack(fmt, last_addr))
                if all([_ in charset for _ in val]):
                    line += f" (\"{Color.colorify(val, string_color)}\"?)"
            except ValueError:
                pass

            gef_print(line)

        if special_line:
            gef_print(special_line)
        return


@register
class ElfInfoCommand(GenericCommand):
    """Display a limited subset of ELF header information. If no argument is provided, the command will
    show information about the current ELF being debugged."""

    _cmdline_ = "elf-info"
    _syntax_  = f"{_cmdline_} [FILE]"
    _example_  = f"{_cmdline_} /bin/ls"

    def __init__(self) -> None:
        super().__init__(complete=gdb.COMPLETE_LOCATION)
        return

    @parse_arguments({}, {"--filename": ""})
    def do_invoke(self, _: List[str], **kwargs: Any) -> None:
        args = kwargs["arguments"]

        if is_qemu_system():
            err("Unsupported")
            return

        filename = args.filename or get_filepath()
        if filename is None:
            return

        try:
            elf = Elf(filename)
        except ValueError as ve:
            err(f"`{filename}` is an invalid value for ELF file")
            return

        data = [
            ("Magic", f"{hexdump(struct.pack('>I', elf.e_magic), show_raw=True)}"),
            ("Class", f"{elf.e_class.value:#x} - {elf.e_class.name}"),
            ("Endianness", f"{elf.e_endianness.value:#x} - {Endianness(elf.e_endianness).name}"),
            ("Version", f"{elf.e_eiversion:#x}"),
            ("OS ABI", f"{elf.e_osabi.value:#x} - {elf.e_osabi.name if elf.e_osabi else ''}"),
            ("ABI Version", f"{elf.e_abiversion:#x}"),
            ("Type", f"{elf.e_type.value:#x} - {elf.e_type.name}"),
            ("Machine", f"{elf.e_machine.value:#x} - {elf.e_machine.name}"),
            ("Program Header Table", f"{format_address(elf.e_phoff)}"),
            ("Section Header Table", f"{format_address(elf.e_shoff)}"),
            ("Header Table", f"{format_address(elf.e_phoff)}"),
            ("ELF Version", f"{elf.e_version:#x}"),
            ("Header size", "{0} ({0:#x})".format(elf.e_ehsize)),
            ("Entry point", f"{format_address(elf.e_entry)}"),
        ]

        for title, content in data:
            gef_print(f"{Color.boldify(f'{title:<22}')}: {content}")

        gef_print("")
        gef_print(titlify("Program Header"))

        gef_print("  [{:>2s}] {:12s} {:>8s} {:>10s} {:>10s} {:>8s} {:>8s} {:5s} {:>8s}".format(
            "#", "Type", "Offset", "Virtaddr", "Physaddr", "FileSiz", "MemSiz", "Flags", "Align"))

        for i, p in enumerate(elf.phdrs):
            p_type = p.p_type.name if p.p_type else ""
            p_flags = str(p.p_flags.name).lstrip("Flag.") if p.p_flags else "???"

            gef_print("  [{:2d}] {:12s} {:#8x} {:#10x} {:#10x} {:#8x} {:#8x} {:5s} {:#8x}".format(
                i, p_type, p.p_offset, p.p_vaddr, p.p_paddr, p.p_filesz, p.p_memsz, p_flags, p.p_align))

        gef_print("")
        gef_print(titlify("Section Header"))
        gef_print("  [{:>2s}] {:20s} {:>15s} {:>10s} {:>8s} {:>8s} {:>8s} {:5s} {:4s} {:4s} {:>8s}".format(
            "#", "Name", "Type", "Address", "Offset", "Size", "EntSiz", "Flags", "Link", "Info", "Align"))

        for i, s in enumerate(elf.shdrs):
            sh_type = s.sh_type.name if s.sh_type else "UNKN"
            sh_flags = str(s.sh_flags).lstrip("Flags.") if s.sh_flags else "UNKN"

            gef_print(f"  [{i:2d}] {s.name:20s} {sh_type:>15s} {s.sh_addr:#10x} {s.sh_offset:#8x} "
                      f"{s.sh_size:#8x} {s.sh_entsize:#8x} {sh_flags:5s} {s.sh_link:#4x} {s.sh_info:#4x} {s.sh_addralign:#8x}")
        return


@register
class EntryPointBreakCommand(GenericCommand):
    """Tries to find best entry point and sets a temporary breakpoint on it. The command will test for
    well-known symbols for entry points, such as `main`, `_main`, etc. defined by
    the setting `entrypoint_symbols`."""

    _cmdline_ = "entry-break"
    _syntax_  = _cmdline_
    _aliases_ = ["start",]

    def __init__(self) -> None:
        super().__init__()
        self["entrypoint_symbols"] = ("main _main start _start", "Possible symbols for entry points")
        return

    def do_invoke(self, argv: List[str]) -> None:
        fpath = get_filepath()
        if fpath is None:
            warn("No executable to debug, use `file` to load a binary")
            return

        if not os.access(fpath, os.X_OK):
            warn(f"The file '{fpath}' is not executable.")
            return

        if is_alive() and not gef.session.qemu_mode:
            warn("gdb is already running")
            return

        bp = None
        entrypoints = self["entrypoint_symbols"].split()

        for sym in entrypoints:
            try:
                value = parse_address(sym)
                info(f"Breaking at '{value:#x}'")
                bp = EntryBreakBreakpoint(sym)
                gdb.execute(f"run {' '.join(argv)}")
                return

            except gdb.error as gdb_error:
                if 'The "remote" target does not support "run".' in str(gdb_error):
                    # this case can happen when doing remote debugging
                    gdb.execute("continue")
                    return
                continue

        # if here, clear the breakpoint if any set
        if bp:
            bp.delete()

        # break at entry point
        entry = gef.binary.entry_point

        self.set_init_tbreak(entry)
        gdb.execute(f"run {' '.join(argv)}")
        return

    def set_init_tbreak(self, addr: int) -> EntryBreakBreakpoint:
        info(f"Breaking at entry-point: {addr:#x}")
        bp = EntryBreakBreakpoint(f"*{addr:#x}")
        return bp


@register
class NamedBreakpointCommand(GenericCommand):
    """Sets a breakpoint and assigns a name to it, which will be shown, when it's hit."""

    _cmdline_ = "name-break"
    _syntax_  = f"{_cmdline_} name [address]"
    _aliases_ = ["nb",]
    _example  = f"{_cmdline_} main *0x4008a9"

    def __init__(self) -> None:
        super().__init__()
        return

    @parse_arguments({"name": "", "address": "*$pc"}, {})
    def do_invoke(self, _: List[str], **kwargs: Any) -> None:
        args = kwargs["arguments"]
        if not args.name:
            err("Missing name for breakpoint")
            self.usage()
            return

        NamedBreakpoint(args.address, args.name)
        return


@register
class ContextCommand(GenericCommand):
    """Displays a comprehensive and modular summary of runtime context. Unless setting `enable` is
    set to False, this command will be spawned automatically every time GDB hits a breakpoint, a
    watchpoint, or any kind of interrupt. By default, it will show panes that contain the register
    states, the stack, and the disassembly code around $pc."""

    _cmdline_ = "context"
    _syntax_  = f"{_cmdline_} [legend|regs|stack|code|args|memory|source|trace|threads|extra]"
    _aliases_ = ["ctx",]

    old_registers: Dict[str, Optional[int]] = {}

    def __init__(self) -> None:
        super().__init__()
        self["enable"] = (True, "Enable/disable printing the context when breaking")
        self["show_source_code_variable_values"] = (True, "Show extra PC context info in the source code")
        self["show_stack_raw"] = (False, "Show the stack pane as raw hexdump (no dereference)")
        self["show_registers_raw"] = (False, "Show the registers pane with raw values (no dereference)")
        self["show_opcodes_size"] = (0, "Number of bytes of opcodes to display next to the disassembly")
        self["peek_calls"] = (True, "Peek into calls")
        self["peek_ret"] = (True, "Peek at return address")
        self["nb_lines_stack"] = (8, "Number of line in the stack pane")
        self["grow_stack_down"] = (False, "Order of stack downward starts at largest down to stack pointer")
        self["nb_lines_backtrace"] = (10, "Number of line in the backtrace pane")
        self["nb_lines_backtrace_before"] = (2, "Number of line in the backtrace pane before selected frame")
        self["nb_lines_threads"] = (-1, "Number of line in the threads pane")
        self["nb_lines_code"] = (6, "Number of instruction after $pc")
        self["nb_lines_code_prev"] = (3, "Number of instruction before $pc")
        self["ignore_registers"] = ("", "Space-separated list of registers not to display (e.g. '$cs $ds $gs')")
        self["clear_screen"] = (True, "Clear the screen before printing the context")
        self["layout"] = ("legend regs stack code args source memory threads trace extra", "Change the order/presence of the context sections")
        self["redirect"] = ("", "Redirect the context information to another TTY")

        self.layout_mapping = {
            "legend": (self.show_legend, None, None),
            "regs": (self.context_regs, None, None),
            "stack": (self.context_stack, None, None),
            "code": (self.context_code, None, None),
            "args": (self.context_args, None, None),
            "memory": (self.context_memory, None, None),
            "source": (self.context_source, None, None),
            "trace": (self.context_trace, None, None),
            "threads": (self.context_threads, None, None),
            "extra": (self.context_additional_information, None, None),
        }

        self.instruction_iterator = gef_disassemble
        return

    def post_load(self) -> None:
        gef_on_continue_hook(self.update_registers)
        gef_on_continue_hook(self.empty_extra_messages)
        return

    def show_legend(self) -> None:
        if gef.config["gef.disable_color"] is True:
            return
        str_color = gef.config["theme.dereference_string"]
        rom0_addr_color = gef.config["theme.address_rom0"]
        iwram_addr_color = gef.config["theme.address_iwram"]
        ewram_addr_color = gef.config["theme.address_ewram"]
        changed_register_color = gef.config["theme.registers_value_changed"]

        gef_print("[ Legend: {} | {} | {} | {} | {} ]".format(Color.colorify("Modified register", changed_register_color),
                                                              Color.colorify("String", str_color),
                                                              Color.colorify("ROM0", rom0_addr_color),
                                                              Color.colorify("EWRAM", ewram_addr_color),
                                                              Color.colorify("IWRAM", iwram_addr_color)))
        return

    @only_if_gdb_running
    def do_invoke(self, argv: List[str]) -> None:
        if not self["enable"] or gef.ui.context_hidden:
            return

        if not all(_ in self.layout_mapping for _ in argv):
            self.usage()
            return

        if len(argv) > 0:
            current_layout = argv
        else:
            current_layout = self["layout"].strip().split()

        if not current_layout:
            return

        self.tty_rows, self.tty_columns = get_terminal_size()

        redirect = self["redirect"]
        if redirect and os.access(redirect, os.W_OK):
            enable_redirect_output(to_file=redirect)

        for section in current_layout:
            if section[0] == "-":
                continue

            try:
                display_pane_function, pane_title_function, condition = self.layout_mapping[section]
                if condition:
                    if not condition():
                        continue
                if pane_title_function:
                    self.context_title(pane_title_function())
                display_pane_function()
            except gdb.MemoryError as e:
                # a MemoryError will happen when $pc is corrupted (invalid address)
                err(str(e))
            except IndexError:
                # the `section` is not present, just skip
                pass

        self.context_title("")

        if self["clear_screen"] and len(argv) == 0:
            clear_screen(redirect)

        if redirect and os.access(redirect, os.W_OK):
            disable_redirect_output()
        return

    def context_title(self, m: Optional[str]) -> None:
        # allow for not displaying a title line
        if m is None:
            return

        line_color = gef.config["theme.context_title_line"]
        msg_color = gef.config["theme.context_title_message"]

        # print an empty line in case of ""
        if not m:
            gef_print(Color.colorify(HORIZONTAL_LINE * self.tty_columns, line_color))
            return

        trail_len = len(m) + 6
        title = ""
        title += Color.colorify("{:{padd}<{width}} ".format("",
                                                            width=max(self.tty_columns - trail_len, 0),
                                                            padd=HORIZONTAL_LINE),
                                line_color)
        title += Color.colorify(m, msg_color)
        title += Color.colorify(" {:{padd}<4}".format("", padd=HORIZONTAL_LINE),
                                line_color)
        gef_print(title)
        return

    def context_regs(self) -> None:
        self.context_title("registers")
        ignored_registers = set(self["ignore_registers"].split())

        if self["show_registers_raw"] is False:
            regs = set(gef.arch.all_registers)
            printable_registers = " ".join(list(regs - ignored_registers))
            gdb.execute(f"registers {printable_registers}")
            return

        widest = l = max(map(len, gef.arch.all_registers))
        l += 5
        l += gef.arch.ptrsize * 2
        nb = get_terminal_size()[1] // l
        i = 1
        line = ""
        changed_color = gef.config["theme.registers_value_changed"]
        regname_color = gef.config["theme.registers_register_name"]

        for reg in gef.arch.all_registers:
            if reg in ignored_registers:
                continue

            try:
                r = gdb.parse_and_eval(reg)
                if r.type.code == gdb.TYPE_CODE_VOID:
                    continue

                new_value_type_flag = r.type.code == gdb.TYPE_CODE_FLAGS
                new_value = int(r)

            except (gdb.MemoryError, gdb.error):
                # If this exception is triggered, it means that the current register
                # is corrupted. Just use the register "raw" value (not eval-ed)
                new_value = gef.arch.register(reg)
                new_value_type_flag = False

            except Exception:
                new_value = 0
                new_value_type_flag = False

            old_value = self.old_registers.get(reg, 0)

            padreg = reg.ljust(widest, " ")
            value = align_address(new_value)
            old_value = align_address(old_value or 0)
            if value == old_value:
                line += f"{Color.colorify(padreg, regname_color)}: "
            else:
                line += f"{Color.colorify(padreg, changed_color)}: "
            if new_value_type_flag:
                line += f"{format_address_spaces(value)} "
            else:
                addr = lookup_address(align_address(int(value)))
                if addr.valid:
                    line += f"{addr!s} "
                else:
                    line += f"{format_address_spaces(value)} "

            if i % nb == 0:
                gef_print(line)
                line = ""
            i += 1

        if line:
            gef_print(line)

        gef_print(f"Flags: {gef.arch.flag_register_to_human()}")
        return

    def context_stack(self) -> None:
        self.context_title("stack")

        show_raw = self["show_stack_raw"]
        nb_lines = self["nb_lines_stack"]

        try:
            sp = gef.arch.sp
            if show_raw is True:
                mem = gef.memory.read(sp, 0x10 * nb_lines)
                gef_print(hexdump(mem, base=sp))
            else:
                gdb.execute(f"dereference -l {nb_lines:d} {sp:#x}")

        except gdb.MemoryError:
            err("Cannot read memory from $SP (corrupted stack pointer?)")

        return

    def addr_has_breakpoint(self, address: int, bp_locations: List[str]) -> bool:
        return any(hex(address) in b for b in bp_locations)

    def context_code(self) -> None:
        nb_insn = self["nb_lines_code"]
        nb_insn_prev = self["nb_lines_code_prev"]
        show_opcodes_size = "show_opcodes_size" in self and self["show_opcodes_size"]
        past_insns_color = gef.config["theme.old_context"]
        cur_insn_color = gef.config["theme.disassemble_current_instruction"]
        pc = gef.arch.pc
        breakpoints = gdb.breakpoints() or []
        bp_locations = [b.location for b in breakpoints if b.location and b.location.startswith("*")]

        frame = gdb.selected_frame()
        arch_name = f"{gef.arch.arch.lower()}:{gef.arch.mode}"

        self.context_title(f"code:{arch_name}")

        try:

            if gef.arch.mode == "THUMB":
                pc -= 1

                # hack to avoid showing undefined instructions after a call in mGBA
                prev_pc_instr = gef_get_instruction_at(pc-2)
                if gef.arch.is_call(prev_pc_instr):
                    pc -= 2

            for insn in self.instruction_iterator(pc, nb_insn, nb_prev=nb_insn_prev):
                line = []
                is_taken  = False
                target    = None
                bp_prefix = Color.redify(BP_GLYPH) if self.addr_has_breakpoint(insn.address, bp_locations) else " "

                if show_opcodes_size == 0:
                    text = str(insn)
                else:
                    insn_fmt = f"{{:{show_opcodes_size}o}}"
                    text = insn_fmt.format(insn)

                if insn.address < pc:
                    line += f"{bp_prefix}  {Color.colorify(text, past_insns_color)}"

                elif insn.address == pc:
                    line += f"{bp_prefix}{Color.colorify(f'{RIGHT_ARROW[1:]}{text}', cur_insn_color)}"

                    if gef.arch.is_conditional_branch(insn):
                        is_taken, reason = gef.arch.is_branch_taken(insn)
                        if is_taken:
                            target = insn.operands[-1].split()[0]
                            reason = f"[Reason: {reason}]" if reason else ""
                            line += Color.colorify(f"\tTAKEN {reason}", "bold green")
                        else:
                            reason = f"[Reason: !({reason})]" if reason else ""
                            line += Color.colorify(f"\tNOT taken {reason}", "bold red")
                    elif gef.arch.is_call(insn) and self["peek_calls"] is True:
                        target = insn.operands[-1].split()[0]
                    elif gef.arch.is_ret(insn) and self["peek_ret"] is True:
                        target = gef.arch.get_ra(insn, frame)

                else:
                    line += f"{bp_prefix}  {text}"

                gef_print("".join(line))

                if target:
                    try:
                        address = int(target, 0) if isinstance(target, str) else target
                    except ValueError:
                        # If the operand isn't an address right now we can't parse it
                        continue
                    for i, tinsn in enumerate(self.instruction_iterator(address, nb_insn)):
                        text= f"   {DOWN_ARROW if i == 0 else ' '}  {tinsn!s}"
                        gef_print(text)
                    break

        except gdb.MemoryError:
            err("Cannot disassemble from $PC")
        return

    def context_args(self) -> None:
        insn = gef_current_instruction(gef.arch.pc)
        if not gef.arch.is_call(insn):
            return

        self.size2type = {
            1: "BYTE",
            2: "WORD",
            4: "DWORD",
            8: "QWORD",
        }

        if insn.operands[-1].startswith(self.size2type[gef.arch.ptrsize]+" PTR"):
            target = "*" + insn.operands[-1].split()[-1]
        elif "$"+insn.operands[0] in gef.arch.all_registers:
            target = f"*{gef.arch.register('$' + insn.operands[0]):#x}"
        else:
            # is there a symbol?
            ops = " ".join(insn.operands)
            if "<" in ops and ">" in ops:
                # extract it
                target = re.sub(r".*<([^\(> ]*).*", r"\1", ops)
            else:
                # it's an address, just use as is
                target = re.sub(r".*(0x[a-fA-F0-9]*).*", r"\1", ops)

        sym = gdb.lookup_global_symbol(target)
        if sym is None:
            self.print_guessed_arguments(target)
            return

        if sym.type.code != gdb.TYPE_CODE_FUNC:
            err(f"Symbol '{target}' is not a function: type={sym.type.code}")
            return

        self.print_arguments_from_symbol(target, sym)
        return

    def print_arguments_from_symbol(self, function_name: str, symbol: "gdb.Symbol") -> None:
        """If symbols were found, parse them and print the argument adequately."""
        args = []

        for i, f in enumerate(symbol.type.fields()):
            _value = gef.arch.get_ith_parameter(i, in_func=False)[1]
            _value = RIGHT_ARROW.join(dereference_from(_value))
            _name = f.name or f"var_{i}"
            _type = f.type.name or self.size2type[f.type.sizeof]
            args.append(f"{_type} {_name} = {_value}")

        self.context_title("arguments")

        if not args:
            gef_print(f"{function_name} (<void>)")
            return

        gef_print(f"{function_name} (\n   "+",\n   ".join(args)+"\n)")
        return

    def print_guessed_arguments(self, function_name: str) -> None:
        """When no symbol, read the current basic block and look for "interesting" instructions."""

        def __get_current_block_start_address() -> Optional[int]:
            pc = gef.arch.pc
            try:
                block = gdb.block_for_pc(pc)
                block_start = block.start if block else gdb_get_nth_previous_instruction_address(pc, 5)
            except RuntimeError:
                block_start = gdb_get_nth_previous_instruction_address(pc, 5)
            return block_start

        parameter_set = set()
        pc = gef.arch.pc
        block_start = __get_current_block_start_address()
        if not block_start:
            return

        function_parameters = gef.arch.function_parameters
        arg_key_color = gef.config["theme.registers_register_name"]

        for insn in self.instruction_iterator(block_start, pc - block_start):
            if not insn.operands:
                continue

            op = "$" + insn.operands[0]
            if op in function_parameters:
                parameter_set.add(op)

        nb_argument = max([function_parameters.index(p)+1 for p in parameter_set], default=0)

        args = []
        for i in range(nb_argument):
            _key, _values = gef.arch.get_ith_parameter(i, in_func=False)
            _values = RIGHT_ARROW.join(dereference_from(_values))
            args.append(f"{Color.colorify(_key, arg_key_color)} = {_values}")

        self.context_title("arguments (guessed)")
        gef_print(f"{function_name} (")
        if args:
            gef_print("   " + ",\n   ".join(args))
        gef_print(")")
        return

    def line_has_breakpoint(self, file_name: str, line_number: int, bp_locations: List[str]) -> bool:
        filename_line = f"{file_name}:{line_number}"
        return any(filename_line in loc for loc in bp_locations)

    def context_source(self) -> None:
        try:
            pc = gef.arch.pc
            symtabline = gdb.find_pc_line(pc)
            symtab = symtabline.symtab
            # we subtract one because the line number returned by gdb start at 1
            line_num = symtabline.line - 1
            if not symtab.is_valid():
                return

            fpath = symtab.fullname()
            with open(fpath, "r") as f:
                lines = [l.rstrip() for l in f.readlines()]

        except Exception:
            return

        file_base_name = os.path.basename(symtab.filename)
        breakpoints = gdb.breakpoints() or []
        bp_locations = [b.location for b in breakpoints if b.location and file_base_name in b.location]
        past_lines_color = gef.config["theme.old_context"]

        nb_line = self["nb_lines_code"]
        fn = symtab.filename
        if len(fn) > 20:
            fn = f"{fn[:15]}[...]{os.path.splitext(fn)[1]}"
        title = f"source:{fn}+{line_num + 1}"
        cur_line_color = gef.config["theme.source_current_line"]
        self.context_title(title)
        show_extra_info = self["show_source_code_variable_values"]

        for i in range(line_num - nb_line + 1, line_num + nb_line):
            if i < 0:
                continue

            bp_prefix = Color.redify(BP_GLYPH) if self.line_has_breakpoint(file_base_name, i + 1, bp_locations) else " "

            if i < line_num:
                gef_print("{}{}".format(bp_prefix, Color.colorify(f"  {i + 1:4d}\t {lines[i]}", past_lines_color)))

            if i == line_num:
                prefix = f"{bp_prefix}{RIGHT_ARROW[1:]}{i + 1:4d}\t "
                leading = len(lines[i]) - len(lines[i].lstrip())
                if show_extra_info:
                    extra_info = self.get_pc_context_info(pc, lines[i])
                    if extra_info:
                        gef_print(f"{' ' * (len(prefix) + leading)}{extra_info}")
                gef_print(Color.colorify(f"{prefix}{lines[i]}", cur_line_color))

            if i > line_num:
                try:
                    gef_print(f"{bp_prefix}  {i + 1:4d}\t {lines[i]}")
                except IndexError:
                    break
        return

    def get_pc_context_info(self, pc: int, line: str) -> str:
        try:
            current_block = gdb.block_for_pc(pc)
            if not current_block or not current_block.is_valid(): return ""
            m = collections.OrderedDict()
            while current_block and not current_block.is_static:
                for sym in current_block:
                    symbol = sym.name
                    if not sym.is_function and re.search(fr"\W{symbol}\W", line):
                        val = gdb.parse_and_eval(symbol)
                        if val.type.code in (gdb.TYPE_CODE_PTR, gdb.TYPE_CODE_ARRAY):
                            addr = int(val.address)
                            addrs = dereference_from(addr)
                            if len(addrs) > 2:
                                addrs = [addrs[0], "[...]", addrs[-1]]

                            f = f" {RIGHT_ARROW} "
                            val = f.join(addrs)
                        elif val.type.code == gdb.TYPE_CODE_INT:
                            val = hex(int(val))
                        else:
                            continue

                        if symbol not in m:
                            m[symbol] = val
                current_block = current_block.superblock

            if m:
                return "// " + ", ".join([f"{Color.yellowify(a)}={b}" for a, b in m.items()])
        except Exception:
            pass
        return ""

    def context_trace(self) -> None:
        self.context_title("trace")

        nb_backtrace = self["nb_lines_backtrace"]
        if nb_backtrace <= 0:
            return

        # backward compat for gdb (gdb < 7.10)
        if not hasattr(gdb, "FrameDecorator"):
            gdb.execute(f"backtrace {nb_backtrace:d}")
            return

        orig_frame = gdb.selected_frame()
        current_frame = gdb.newest_frame()
        frames = [current_frame]
        while current_frame != orig_frame:
            current_frame = current_frame.older()
            frames.append(current_frame)

        nb_backtrace_before = self["nb_lines_backtrace_before"]
        level = max(len(frames) - nb_backtrace_before - 1, 0)
        current_frame = frames[level]

        while current_frame:
            current_frame.select()
            if not current_frame.is_valid():
                continue

            pc = current_frame.pc()
            name = current_frame.name()
            items = []
            items.append(f"{pc:#x}")
            if name:
                frame_args = gdb.FrameDecorator.FrameDecorator(current_frame).frame_args() or []
                m = "{}({})".format(Color.greenify(name),
                                    ", ".join(["{}={!s}".format(Color.yellowify(x.sym),
                                                                x.sym.value(current_frame)) for x in frame_args]))
                items.append(m)
            else:
                try:
                    insn = next(gef_disassemble(pc, 1))
                except gdb.MemoryError:
                    break

                # check if the gdb symbol table may know the address
                sym_found = gdb_get_location_from_symbol(pc)
                symbol = ""
                if sym_found:
                    sym_name, offset = sym_found
                    symbol = f" <{sym_name}+{offset:x}> "

                items.append(Color.redify(f"{symbol}{insn.mnemonic} {', '.join(insn.operands)}"))

            gef_print("[{}] {}".format(Color.colorify(f"#{level}", "bold green" if current_frame == orig_frame else "bold pink"),
                                       RIGHT_ARROW.join(items)))
            current_frame = current_frame.older()
            level += 1
            nb_backtrace -= 1
            if nb_backtrace == 0:
                break

        orig_frame.select()
        return

    def context_threads(self) -> None:
        def reason() -> str:
            res = gdb.execute("info program", to_string=True)
            if not res:
                return "NOT RUNNING"

            for line in res.splitlines():
                line = line.strip()
                if line.startswith("It stopped with signal "):
                    return line.replace("It stopped with signal ", "").split(",", 1)[0]
                if line == "The program being debugged is not being run.":
                    return "NOT RUNNING"
                if line == "It stopped at a breakpoint that has since been deleted.":
                    return "TEMPORARY BREAKPOINT"
                if line.startswith("It stopped at breakpoint "):
                    return "BREAKPOINT"
                if line == "It stopped after being stepped.":
                    return "SINGLE STEP"

            return "STOPPED"

        self.context_title("threads")

        threads = gdb.selected_inferior().threads()[::-1]
        idx = self["nb_lines_threads"]
        if idx > 0:
            threads = threads[0:idx]

        if idx == 0:
            return

        if not threads:
            err("No thread selected")
            return

        selected_thread = gdb.selected_thread()
        selected_frame = gdb.selected_frame()

        for i, thread in enumerate(threads):
            line = f"[{Color.colorify(f'#{i:d}', 'bold green' if thread == selected_thread else 'bold pink')}] Id {thread.num:d}, "
            if thread.name:
                line += f"""Name: "{thread.name}", """
            if thread.is_running():
                line += Color.colorify("running", "bold green")
            elif thread.is_stopped():
                line += Color.colorify("stopped", "bold red")
                thread.switch()
                frame = gdb.selected_frame()
                frame_name = frame.name()

                # check if the gdb symbol table may know the address
                if not frame_name:
                    sym_found = gdb_get_location_from_symbol(frame.pc())
                    if sym_found:
                        sym_name, offset = sym_found
                        frame_name = f"<{sym_name}+{offset:x}>"

                line += (f" {Color.colorify(f'{frame.pc():#x}', 'blue')} in "
                         f"{Color.colorify(frame_name or '??', 'bold yellow')} (), "
                         f"reason: {Color.colorify(reason(), 'bold pink')}")
            elif thread.is_exited():
                line += Color.colorify("exited", "bold yellow")
            gef_print(line)
            i += 1

        selected_thread.switch()
        selected_frame.select()
        return

    def context_additional_information(self) -> None:
        if not gef.ui.context_messages:
            return

        self.context_title("extra")
        for level, text in gef.ui.context_messages:
            if level == "error": err(text)
            elif level == "warn": warn(text)
            elif level == "success": ok(text)
            else: info(text)
        return

    def context_memory(self) -> None:
        for address, opt in sorted(gef.ui.watches.items()):
            sz, fmt = opt[0:2]
            self.context_title(f"memory:{address:#x}")
            if fmt == "pointers":
                gdb.execute(f"dereference -l {sz:d} {address:#x}")
            else:
                gdb.execute(f"hexdump {fmt} -s {sz:d} {address:#x}")

    @classmethod
    def update_registers(cls, _) -> None:
        for reg in gef.arch.all_registers:
            try:
                cls.old_registers[reg] = gef.arch.register(reg)
            except Exception:
                cls.old_registers[reg] = 0
        return

    def empty_extra_messages(self, _) -> None:
        gef.ui.context_messages.clear()
        return


@register
class MemoryCommand(GenericCommand):
    """Add or remove address ranges to the memory view."""
    _cmdline_ = "memory"
    _syntax_  = f"{_cmdline_} (watch|unwatch|reset|list)"

    def __init__(self) -> None:
        super().__init__(prefix=True)
        return

    @only_if_gdb_running
    def do_invoke(self, argv: List[str]) -> None:
        self.usage()
        return


@register
class MemoryWatchCommand(GenericCommand):
    """Adds address ranges to the memory view."""
    _cmdline_ = "memory watch"
    _syntax_  = f"{_cmdline_} ADDRESS [SIZE] [(qword|dword|word|byte|pointers)]"
    _example_ = (f"\n{_cmdline_} 0x603000 0x100 byte"
                 f"\n{_cmdline_} $sp")

    def __init__(self) -> None:
        super().__init__(complete=gdb.COMPLETE_LOCATION)
        return

    @only_if_gdb_running
    def do_invoke(self, argv: List[str]) -> None:
        if len(argv) not in (1, 2, 3):
            self.usage()
            return

        address = parse_address(argv[0])
        size    = parse_address(argv[1]) if len(argv) > 1 else 0x10
        group   = "byte"

        if len(argv) == 3:
            group = argv[2].lower()
            if group not in ("qword", "dword", "word", "byte", "pointers"):
                warn(f"Unexpected grouping '{group}'")
                self.usage()
                return
        else:
            if gef.arch.ptrsize == 4:
                group = "dword"
            elif gef.arch.ptrsize == 8:
                group = "qword"

        gef.ui.watches[address] = (size, group)
        ok(f"Adding memwatch to {address:#x}")
        return


@register
class MemoryUnwatchCommand(GenericCommand):
    """Removes address ranges to the memory view."""
    _cmdline_ = "memory unwatch"
    _syntax_  = f"{_cmdline_} ADDRESS"
    _example_ = (f"\n{_cmdline_} 0x603000"
                 f"\n{_cmdline_} $sp")

    def __init__(self) -> None:
        super().__init__(complete=gdb.COMPLETE_LOCATION)
        return

    @only_if_gdb_running
    def do_invoke(self, argv: List[str]) -> None:
        if not argv:
            self.usage()
            return

        address = parse_address(argv[0])
        res = gef.ui.watches.pop(address, None)
        if not res:
            warn(f"You weren't watching {address:#x}")
        else:
            ok(f"Removed memwatch of {address:#x}")
        return


@register
class MemoryWatchResetCommand(GenericCommand):
    """Removes all watchpoints."""
    _cmdline_ = "memory reset"
    _syntax_  = f"{_cmdline_}"

    @only_if_gdb_running
    def do_invoke(self, _: List[str]) -> None:
        gef.ui.watches.clear()
        ok("Memory watches cleared")
        return


@register
class MemoryWatchListCommand(GenericCommand):
    """Lists all watchpoints to display in context layout."""
    _cmdline_ = "memory list"
    _syntax_  = f"{_cmdline_}"

    @only_if_gdb_running
    def do_invoke(self, _: List[str]) -> None:
        if not gef.ui.watches:
            info("No memory watches")
            return

        info("Memory watches:")
        for address, opt in sorted(gef.ui.watches.items()):
            gef_print(f"- {address:#x} ({opt[0]}, {opt[1]})")
        return


@register
class HexdumpCommand(GenericCommand):
    """Display SIZE lines of hexdump from the memory location pointed by LOCATION."""

    _cmdline_ = "hexdump"
    _syntax_  = f"{_cmdline_} (qword|dword|word|byte) [LOCATION] [--size SIZE] [--reverse]"
    _example_ = f"{_cmdline_} byte $rsp --size 16 --reverse"

    def __init__(self) -> None:
        super().__init__(complete=gdb.COMPLETE_LOCATION, prefix=True)
        self["always_show_ascii"] = (False, "If true, hexdump will always display the ASCII dump")
        self.format: Optional[str] = None
        self.__last_target = "$sp"
        return

    @only_if_gdb_running
    @parse_arguments({"address": "",}, {("--reverse", "-r"): True, ("--size", "-s"): 0})
    def do_invoke(self, _: List[str], **kwargs: Any) -> None:
        valid_formats = ["byte", "word", "dword", "qword"]
        if not self.format or self.format not in valid_formats:
            err("Invalid command")
            return

        args = kwargs["arguments"]
        target = args.address or self.__last_target
        start_addr = parse_address(target)
        read_from = align_address(start_addr)

        if self.format == "byte":
            read_len = args.size or 0x40
            read_from += self.repeat_count * read_len
            mem = gef.memory.read(read_from, read_len)
            lines = hexdump(mem, base=read_from).splitlines()
        else:
            read_len = args.size or 0x10
            lines = self._hexdump(read_from, read_len, self.format, self.repeat_count * read_len)

        if args.reverse:
            lines.reverse()

        self.__last_target = target
        gef_print("\n".join(lines))
        return

    def _hexdump(self, start_addr: int, length: int, arrange_as: str, offset: int = 0) -> List[str]:
        endianness = gef.arch.endianness

        base_address_color = gef.config["theme.dereference_base_address"]
        show_ascii = gef.config["hexdump.always_show_ascii"]

        formats = {
            "qword": ("Q", 8),
            "dword": ("I", 4),
            "word": ("H", 2),
        }

        r, l = formats[arrange_as]
        fmt_str = f"{{base}}{VERTICAL_LINE}+{{offset:#06x}}   {{sym}}{{val:#0{l*2+2}x}}   {{text}}"
        fmt_pack = f"{endianness!s}{r}"
        lines = []

        i = 0
        text = ""
        while i < length:
            cur_addr = start_addr + (i + offset) * l
            sym = gdb_get_location_from_symbol(cur_addr)
            sym = "<{:s}+{:04x}> ".format(*sym) if sym else ""
            mem = gef.memory.read(cur_addr, l)
            val = struct.unpack(fmt_pack, mem)[0]
            if show_ascii:
                text = "".join([chr(b) if 0x20 <= b < 0x7F else "." for b in mem])
            lines.append(fmt_str.format(base=Color.colorify(format_address(cur_addr), base_address_color),
                                        offset=(i + offset) * l, sym=sym, val=val, text=text))
            i += 1

        return lines


@register
class HexdumpQwordCommand(HexdumpCommand):
    """Display SIZE lines of hexdump as QWORD from the memory location pointed by ADDRESS."""

    _cmdline_ = "hexdump qword"
    _syntax_  = f"{_cmdline_} [ADDRESS] [[L][SIZE]] [REVERSE]"
    _example_ = f"{_cmdline_} qword $rsp L16 REVERSE"

    def __init__(self) -> None:
        super().__init__()
        self.format = "qword"
        return


@register
class HexdumpDwordCommand(HexdumpCommand):
    """Display SIZE lines of hexdump as DWORD from the memory location pointed by ADDRESS."""

    _cmdline_ = "hexdump dword"
    _syntax_  = f"{_cmdline_} [ADDRESS] [[L][SIZE]] [REVERSE]"
    _example_ = f"{_cmdline_} $esp L16 REVERSE"

    def __init__(self) -> None:
        super().__init__()
        self.format = "dword"
        return


@register
class HexdumpWordCommand(HexdumpCommand):
    """Display SIZE lines of hexdump as WORD from the memory location pointed by ADDRESS."""

    _cmdline_ = "hexdump word"
    _syntax_  = f"{_cmdline_} [ADDRESS] [[L][SIZE]] [REVERSE]"
    _example_ = f"{_cmdline_} $esp L16 REVERSE"

    def __init__(self) -> None:
        super().__init__()
        self.format = "word"
        return


@register
class HexdumpByteCommand(HexdumpCommand):
    """Display SIZE lines of hexdump as BYTE from the memory location pointed by ADDRESS."""

    _cmdline_ = "hexdump byte"
    _syntax_  = f"{_cmdline_} [ADDRESS] [[L][SIZE]] [REVERSE]"
    _example_ = f"{_cmdline_} $rsp L16"

    def __init__(self) -> None:
        super().__init__()
        self.format = "byte"
        return


@register
class PatchCommand(GenericCommand):
    """Write specified values to the specified address."""

    _cmdline_ = "patch"
    _syntax_  = (f"{_cmdline_} (qword|dword|word|byte) LOCATION VALUES\n"
                 f"{_cmdline_} string LOCATION \"double-escaped string\"")
    SUPPORTED_SIZES = {
        "qword": (8, "Q"),
        "dword": (4, "L"),
        "word": (2, "H"),
        "byte": (1, "B"),
    }

    def __init__(self) -> None:
        super().__init__(prefix=True, complete=gdb.COMPLETE_LOCATION)
        self.format: Optional[str] = None
        return

    @only_if_gdb_running
    @parse_arguments({"location": "", "values": ["", ]}, {})
    def do_invoke(self, _: List[str], **kwargs: Any) -> None:
        args = kwargs["arguments"]
        if not self.format or self.format not in self.SUPPORTED_SIZES:
            self.usage()
            return

        if not args.location or not args.values:
            self.usage()
            return

        addr = align_address(parse_address(args.location))
        size, fcode = self.SUPPORTED_SIZES[self.format]
        values = args.values

        if size == 1:
            if values[0].startswith("$_gef"):
                var_name = values[0]
                try:
                    values = str(gdb.parse_and_eval(var_name)).lstrip("{").rstrip("}").replace(",","").split(" ")
                except:
                    gef_print(f"Bad variable specified, check value with command: p {var_name}")
                    return

        d = str(gef.arch.endianness)
        for value in values:
            value = parse_address(value) & ((1 << size * 8) - 1)
            vstr = struct.pack(d + fcode, value)
            gef.memory.write(addr, vstr, length=size)
            addr += size
        return


@register
class PatchQwordCommand(PatchCommand):
    """Write specified QWORD to the specified address."""

    _cmdline_ = "patch qword"
    _syntax_  = f"{_cmdline_} LOCATION QWORD1 [QWORD2 [QWORD3..]]"
    _example_ = f"{_cmdline_} $rip 0x4141414141414141"

    def __init__(self) -> None:
        super().__init__()
        self.format = "qword"
        return


@register
class PatchDwordCommand(PatchCommand):
    """Write specified DWORD to the specified address."""

    _cmdline_ = "patch dword"
    _syntax_  = f"{_cmdline_} LOCATION DWORD1 [DWORD2 [DWORD3..]]"
    _example_ = f"{_cmdline_} $rip 0x41414141"

    def __init__(self) -> None:
        super().__init__()
        self.format = "dword"
        return


@register
class PatchWordCommand(PatchCommand):
    """Write specified WORD to the specified address."""

    _cmdline_ = "patch word"
    _syntax_  = f"{_cmdline_} LOCATION WORD1 [WORD2 [WORD3..]]"
    _example_ = f"{_cmdline_} $rip 0x4141"

    def __init__(self) -> None:
        super().__init__()
        self.format = "word"
        return


@register
class PatchByteCommand(PatchCommand):
    """Write specified BYTE to the specified address."""

    _cmdline_ = "patch byte"
    _syntax_  = f"{_cmdline_} LOCATION BYTE1 [BYTE2 [BYTE3..]]"
    _example_ = f"{_cmdline_} $pc 0x41 0x41 0x41 0x41 0x41"

    def __init__(self) -> None:
        super().__init__()
        self.format = "byte"
        return


@register
class PatchStringCommand(GenericCommand):
    """Write specified string to the specified memory location pointed by ADDRESS."""

    _cmdline_ = "patch string"
    _syntax_  = f"{_cmdline_} ADDRESS \"double backslash-escaped string\""
    _example_ = f"{_cmdline_} $sp \"GEFROCKS\""

    @only_if_gdb_running
    def do_invoke(self, argv: List[str]) -> None:
        argc = len(argv)
        if argc != 2:
            self.usage()
            return

        location, s = argv[0:2]
        addr = align_address(parse_address(location))

        try:
            s = codecs.escape_decode(s)[0]
        except binascii.Error:
            gef_print(f"Could not decode '\\xXX' encoded string \"{s}\"")
            return

        gef.memory.write(addr, s, len(s))
        return


@lru_cache()
def dereference_from(address: int) -> List[str]:
    if not is_alive():
        return [format_address(address),]

    code_color = gef.config["theme.dereference_code"]
    string_color = gef.config["theme.dereference_string"]
    max_recursion = gef.config["dereference.max_recursion"] or 10
    addr = lookup_address(align_address(address))
    msg = [format_address(addr.value),]
    seen_addrs = set()

    while addr.section and max_recursion:
        if addr.value in seen_addrs:
            msg.append("[loop detected]")
            break
        seen_addrs.add(addr.value)

        max_recursion -= 1

        # Don't dereference BIOS addresses
        if addr.is_in_bios():
            break

        # Is this value a pointer or a value?
        # -- If it's a pointer, dereference
        deref = addr.dereference()
        if deref is None:
            # if here, dereferencing addr has triggered a MemoryError, no need to go further
            msg.append(str(addr))
            break

        new_addr = lookup_address(deref)
        if new_addr.valid:
            addr = new_addr
            msg.append(str(addr))
            continue

        # -- Otherwise try to parse the value
        if addr.section:
            if addr.is_in_rom0() and not is_ascii_string(addr.value):
                insn = gef_current_instruction(addr.value)
                insn_str = f"{insn.location} {insn.mnemonic} {', '.join(insn.operands)}"
                msg.append(Color.colorify(insn_str, code_color))
                break

            elif addr.section.permission & Permission.READ:
                if is_ascii_string(addr.value):
                    s = gef.memory.read_cstring(addr.value)
                    if len(s) < gef.arch.ptrsize:
                        txt = f'{format_address(deref)} ("{Color.colorify(s, string_color)}"?)'
                    elif len(s) > 50:
                        txt = Color.colorify(f'"{s[:50]}[...]"', string_color)
                    else:
                        txt = Color.colorify(f'"{s}"', string_color)

                    msg.append(txt)
                    break

        # if not able to parse cleanly, simply display and break
        val = "{:#0{ma}x}".format(int(deref & 0xFFFFFFFF), ma=(gef.arch.ptrsize * 2 + 2))
        msg.append(val)
        break

    return msg


@register
class DereferenceCommand(GenericCommand):
    """Dereference recursively from an address and display information. This acts like WinDBG `dps`
    command."""

    _cmdline_ = "dereference"
    _syntax_  = f"{_cmdline_} [-h] [--length LENGTH] [--reference REFERENCE] [address]"
    _aliases_ = ["telescope", ]
    _example_ = f"{_cmdline_} --length 20 --reference $sp+0x10 $sp"

    def __init__(self) -> None:
        super().__init__(complete=gdb.COMPLETE_LOCATION)
        self["max_recursion"] = (7, "Maximum level of pointer recursion")
        return

    @staticmethod
    def pprint_dereferenced(addr: int, idx: int, base_offset: int = 0) -> str:
        base_address_color = gef.config["theme.dereference_base_address"]
        registers_color = gef.config["theme.dereference_register_value"]

        sep = f" {RIGHT_ARROW} "
        memalign = gef.arch.ptrsize

        offset = idx * memalign
        current_address = align_address(addr + offset)
        addrs = dereference_from(current_address)
        l = ""
        addr_l = format_address(int(addrs[0], 16))
        l += "{}{}{:+#07x}: {:{ma}s}".format(Color.colorify(addr_l, base_address_color),
                                             VERTICAL_LINE, base_offset+offset,
                                             sep.join(addrs[1:]), ma=(memalign*2 + 2))

        register_hints = []

        for regname in gef.arch.all_registers:
            regvalue = gef.arch.register(regname)
            if current_address == regvalue:
                register_hints.append(regname)

        if register_hints:
            m = f"\t{LEFT_ARROW}{', '.join(list(register_hints))}"
            l += Color.colorify(m, registers_color)

        offset += memalign
        return l

    @only_if_gdb_running
    @parse_arguments({"address": "$sp"}, {("-r", "--reference"): "", ("-l", "--length"): 10})
    def do_invoke(self, _: List[str], **kwargs: Any) -> None:
        args = kwargs["arguments"]
        nb = args.length

        target = args.address
        target_addr = parse_address(target)

        reference = args.reference or target
        ref_addr = parse_address(reference)

        if process_lookup_address(target_addr) is None:
            err(f"Unmapped address: '{target}'")
            return

        if process_lookup_address(ref_addr) is None:
            err(f"Unmapped address: '{reference}'")
            return

        if gef.config["context.grow_stack_down"] is True:
            from_insnum = nb * (self.repeat_count + 1) - 1
            to_insnum = self.repeat_count * nb - 1
            insnum_step = -1
        else:
            from_insnum = 0 + self.repeat_count * nb
            to_insnum = nb * (self.repeat_count + 1)
            insnum_step = 1

        start_address = align_address(target_addr)
        base_offset = start_address - align_address(ref_addr)

        for i in range(from_insnum, to_insnum, insnum_step):
            gef_print(DereferenceCommand.pprint_dereferenced(start_address, i, base_offset))

        return


@register
class ResetCacheCommand(GenericCommand):
    """Reset cache of all stored data. This command is here for debugging and test purposes, GEF
    handles properly the cache reset under "normal" scenario."""

    _cmdline_ = "reset-cache"
    _syntax_  = _cmdline_

    def do_invoke(self, _: List[str]) -> None:
        reset_all_caches()
        return


@register
class MMapCommand(GenericCommand):
    """Display a comprehensive layout of the memory mapping. If a filter argument, GEF will
    filter out the mapping whose pathname do not match that filter."""

    _cmdline_ = "mmap"
    _syntax_  = f"{_cmdline_} [FILTER]"
    _example_ = f"{_cmdline_} EWRAM"

    @only_if_gdb_running
    def do_invoke(self, argv: List[str]) -> None:
        mmap = gef.memory.maps
        if not mmap:
            err("No address mapping information found")
            return

        color = gef.config["theme.table_heading"]

        headers = ["Start", "End", "Perm", "Name"]
        gef_print(Color.colorify("{:<{w}s}{:<{w}s}{:<3s} {:s}".format(*headers, w=gef.arch.ptrsize*2+3), color))

        for entry in mmap:
            if not argv:
                self.print_entry(entry)
                continue
            if argv[0] in entry.name:
                self.print_entry(entry)
            elif self.is_integer(argv[0]):
                addr = int(argv[0], 0)
                if addr >= entry.start and addr < entry.end:
                    self.print_entry(entry)
        return

    def print_entry(self, entry: Section) -> None:
        line_color = ""
        if entry.name == "ROM0":
            line_color = gef.config["theme.address_rom0"]
        elif entry.name == "IWRAM":
            line_color = gef.config["theme.address_iwram"]
        elif entry.name == "EWRAM":
            line_color = gef.config["theme.address_ewram"]

        l = [
            Color.colorify(format_address(entry.start), line_color),
            Color.colorify(format_address(entry.end), line_color),
        ]
        l.append(Color.colorify(str(entry.permission), line_color))
        l.append(Color.colorify(" "+entry.name, line_color))

        line = " ".join(l)

        gef_print(line)
        return

    def is_integer(self, n: str) -> bool:
        try:
            int(n, 0)
        except ValueError:
            return False
        return True


@register
class XFilesCommand(GenericCommand):
    """Shows all libraries (and sections) loaded by binary. This command extends the GDB command
    `info files`, by retrieving more information from extra sources, and providing a better
    display. If an argument FILE is given, the output will grep information related to only that file.
    If an argument name is also given, the output will grep to the name within FILE."""

    _cmdline_ = "xfiles"
    _syntax_  = f"{_cmdline_} [FILE [NAME]]"
    _example_ = f"\n{_cmdline_} cart.elf"

    @only_if_gdb_running
    def do_invoke(self, argv: List[str]) -> None:
        color = gef.config["theme.table_heading"]
        headers = ["Start", "End", "Name", "File"]
        gef_print(Color.colorify("{:<{w}s}{:<{w}s}{:<21s} {:s}".format(*headers, w=gef.arch.ptrsize*2+3), color))

        filter_by_file = argv[0] if argv and argv[0] else None
        filter_by_name = argv[1] if len(argv) > 1 and argv[1] else None

        for xfile in get_info_files():
            if filter_by_file:
                if filter_by_file not in xfile.filename:
                    continue
                if filter_by_name and filter_by_name not in xfile.name:
                    continue

            l = [
                format_address(xfile.zone_start),
                format_address(xfile.zone_end),
                f"{xfile.name:<21s}",
                xfile.filename,
            ]
            gef_print(" ".join(l))
        return


@register
class XAddressInfoCommand(GenericCommand):
    """Retrieve and display runtime information for the location(s) given as parameter."""

    _cmdline_ = "xinfo"
    _syntax_  = f"{_cmdline_} LOCATION"
    _example_ = f"{_cmdline_} $pc"

    def __init__(self) -> None:
        super().__init__(complete=gdb.COMPLETE_LOCATION)
        return

    @only_if_gdb_running
    def do_invoke(self, argv: List[str]) -> None:
        if not argv:
            err("At least one valid address must be specified")
            self.usage()
            return

        for sym in argv:
            try:
                addr = align_address(parse_address(sym))
                gef_print(titlify(f"xinfo: {addr:#x}"))
                self.infos(addr)

            except gdb.error as gdb_err:
                err(f"{gdb_err}")
        return

    def infos(self, address: int) -> None:
        addr = lookup_address(address)
        if not addr.valid:
            warn(f"Cannot reach {address:#x} in memory space")
            return

        sect = addr.section
        info = addr.info

        if sect:
            gef_print(f"Section: {format_address(sect.start)} {RIGHT_ARROW} "
                      f"{format_address(sect.end)} (size={sect.end-sect.start:#x})"
                      f"\nPermissions: {sect.permission}"
                      f"\nName: {sect.name}"
                      f"\nOffset (from page): {addr.value-sect.start:#x}")

        if info:
            gef_print(f"Segment: {info.name} "
                      f"({format_address(info.zone_start)}-{format_address(info.zone_end)})"
                      f"\nOffset (from segment): {addr.value-info.zone_start:#x}")

        sym = gdb_get_location_from_symbol(address)
        if sym:
            name, offset = sym
            msg = f"Symbol: {name}"
            if offset:
                msg += f"+{offset:d}"
            gef_print(msg)

        return


@register
class XorMemoryCommand(GenericCommand):
    """XOR a block of memory. The command allows to simply display the result, or patch it
    runtime at runtime."""

    _cmdline_ = "xor-memory"
    _syntax_  = f"{_cmdline_} (display|patch) ADDRESS SIZE KEY"

    def __init__(self) -> None:
        super().__init__(prefix=True)
        return

    def do_invoke(self, _: List[str]) -> None:
        self.usage()
        return


@register
class XorMemoryDisplayCommand(GenericCommand):
    """Display a block of memory pointed by ADDRESS by xor-ing each byte with KEY. The key must be
    provided in hexadecimal format."""

    _cmdline_ = "xor-memory display"
    _syntax_  = f"{_cmdline_} ADDRESS SIZE KEY"
    _example_ = f"{_cmdline_} $sp 16 41414141"

    @only_if_gdb_running
    def do_invoke(self, argv: List[str]) -> None:
        if len(argv) != 3:
            self.usage()
            return

        address = parse_address(argv[0])
        length = int(argv[1], 0)
        key = argv[2]
        block = gef.memory.read(address, length)
        info(f"Displaying XOR-ing {address:#x}-{address + len(block):#x} with {key!r}")

        gef_print(titlify("Original block"))
        gef_print(hexdump(block, base=address))

        gef_print(titlify("XOR-ed block"))
        gef_print(hexdump(xor(block, key), base=address))
        return


@register
class XorMemoryPatchCommand(GenericCommand):
    """Patch a block of memory pointed by ADDRESS by xor-ing each byte with KEY. The key must be
    provided in hexadecimal format."""

    _cmdline_ = "xor-memory patch"
    _syntax_  = f"{_cmdline_} ADDRESS SIZE KEY"
    _example_ = f"{_cmdline_} $sp 16 41414141"

    @only_if_gdb_running
    def do_invoke(self, argv: List[str]) -> None:
        if len(argv) != 3:
            self.usage()
            return

        address = parse_address(argv[0])
        length = int(argv[1], 0)
        key = argv[2]
        block = gef.memory.read(address, length)
        info(f"Patching XOR-ing {address:#x}-{address + len(block):#x} with {key!r}")
        xored_block = xor(block, key)
        gef.memory.write(address, xored_block, length)
        return


@register
class TraceRunCommand(GenericCommand):
    """Create a runtime trace of all instructions executed from $pc to LOCATION specified. The
    trace is stored in a text file that can be next imported in IDA Pro to visualize the runtime
    path."""

    _cmdline_ = "trace-run"
    _syntax_  = f"{_cmdline_} LOCATION [MAX_CALL_DEPTH]"
    _example_ = f"{_cmdline_} 0x555555554610"

    def __init__(self) -> None:
        super().__init__(self._cmdline_, complete=gdb.COMPLETE_LOCATION)
        self["max_tracing_recursion"] = (1, "Maximum depth of tracing")
        self["tracefile_prefix"] = ("./gef-trace-", "Specify the tracing output file prefix")
        return

    @only_if_gdb_running
    def do_invoke(self, argv: List[str]) -> None:
        if len(argv) not in (1, 2):
            self.usage()
            return

        if len(argv) == 2 and argv[1].isdigit():
            depth = int(argv[1])
        else:
            depth = 1

        try:
            loc_start   = gef.arch.pc
            loc_end     = parse_address(argv[0])
        except gdb.error as e:
            err(f"Invalid location: {e}")
            return

        self.trace(loc_start, loc_end, depth)
        return

    def get_frames_size(self) -> int:
        n = 0
        f = gdb.newest_frame()
        while f:
            n += 1
            f = f.older()
        return n

    def trace(self, loc_start: int, loc_end: int, depth: int) -> None:
        info(f"Tracing from {loc_start:#x} to {loc_end:#x} (max depth={depth:d})")
        logfile = f"{self['tracefile_prefix']}{loc_start:#x}-{loc_end:#x}.txt"
        with RedirectOutputContext(to=logfile):
            hide_context()
            self.start_tracing(loc_start, loc_end, depth)
            unhide_context()
        ok(f"Done, logfile stored as '{logfile}'")
        info("Hint: import logfile with `ida_color_gdb_trace.py` script in IDA to visualize path")
        return

    def start_tracing(self, loc_start: int, loc_end: int, depth: int) -> None:
        loc_cur = loc_start
        frame_count_init = self.get_frames_size()

        gef_print("#",
                  f"# Execution tracing of {get_filepath()}",
                  f"# Start address: {format_address(loc_start)}",
                  f"# End address: {format_address(loc_end)}",
                  f"# Recursion level: {depth:d}",
                  "# automatically generated by gef.py",
                  "#\n", sep="\n")

        while loc_cur != loc_end:
            try:
                delta = self.get_frames_size() - frame_count_init

                if delta <= depth:
                    gdb.execute("stepi")
                else:
                    gdb.execute("finish")

                loc_cur = gef.arch.pc
                gdb.flush()

            except gdb.error as e:
                gef_print("#",
                          f"# Execution interrupted at address {format_address(loc_cur)}",
                          f"# Exception: {e}",
                          "#\n", sep="\n")
                break

        return


@register
class PatternCommand(GenericCommand):
    """Generate or Search a De Bruijn Sequence of unique substrings of length N
    and a total length of LENGTH. The default value of N is set to match the
    currently loaded architecture."""

    _cmdline_ = "pattern"
    _syntax_  = f"{_cmdline_} (create|search) ARGS"

    def __init__(self) -> None:
        super().__init__(prefix=True)
        self["length"] = (1024, "Default length of a cyclic buffer to generate")
        return

    def do_invoke(self, _: List[str]) -> None:
        self.usage()
        return


@register
class PatternCreateCommand(GenericCommand):
    """Generate a De Bruijn Sequence of unique substrings of length N and a
    total length of LENGTH. The default value of N is set to match the currently
    loaded architecture."""

    _cmdline_ = "pattern create"
    _syntax_  = f"{_cmdline_} [-h] [-n N] [length]"
    _example_ = f"{_cmdline_} 4096"

    @parse_arguments({"length": 0}, {("-n", "--n"): 0})
    def do_invoke(self, _: List[str], **kwargs: Any) -> None:
        args = kwargs["arguments"]
        length = args.length or gef.config["pattern.length"]
        n = args.n or gef.arch.ptrsize
        info(f"Generating a pattern of {length:d} bytes (n={n:d})")
        pattern_str = gef_pystring(generate_cyclic_pattern(length, n))
        gef_print(pattern_str)
        ok(f"Saved as '{gef_convenience(pattern_str)}'")
        return


@register
class PatternSearchCommand(GenericCommand):
    """Search a De Bruijn Sequence of unique substrings of length N and a
    maximum total length of MAX_LENGTH. The default value of N is set to match
    the currently loaded architecture. The PATTERN argument can be a GDB symbol
    (such as a register name), a string or a hexadecimal value"""

    _cmdline_ = "pattern search"
    _syntax_  = f"{_cmdline_} [-h] [-n N] [--max-length MAX_LENGTH] [pattern]"
    _example_ = [f"{_cmdline_} $pc",
                 f"{_cmdline_} 0x61616164",
                 f"{_cmdline_} aaab"]
    _aliases_ = ["pattern offset"]

    @only_if_gdb_running
    @parse_arguments({"pattern": ""}, {("--period", "-n"): 0, ("--max-length", "-l"): 0})
    def do_invoke(self, _: List[str], **kwargs: Any) -> None:
        args = kwargs["arguments"]
        if not args.pattern:
            warn("No pattern provided")
            return
        max_length = args.max_length or gef.config["pattern.length"]
        n = args.period or gef.arch.ptrsize
        if n not in (2, 4, 8) or n > gef.arch.ptrsize:
            err("Incorrect value for period")
            return
        self.search(args.pattern, max_length, n)
        return

    def search(self, pattern: str, size: int, period: int) -> None:
        pattern_be, pattern_le = None, None

        # 1. check if it's a symbol (like "$sp" or "0x1337")
        symbol = safe_parse_and_eval(pattern)
        if symbol:
            addr = int(abs(symbol))
            dereferenced_value = dereference(addr)
            if dereferenced_value:
                addr = int(abs(dereferenced_value))
            mask = (1<<(8 * period))-1
            addr &= mask
            pattern_le = addr.to_bytes(period, 'little')
            pattern_be = addr.to_bytes(period, 'big')
        else:
            # 2. assume it's a plain string
            pattern_be = gef_pybytes(pattern)
            pattern_le = gef_pybytes(pattern[::-1])

        info(f"Searching for '{pattern_le.hex()}'/'{pattern_be.hex()}' with period={period}")
        cyclic_pattern = generate_cyclic_pattern(size, period)
        off = cyclic_pattern.find(pattern_le)
        if off >= 0:
            ok(f"Found at offset {off:d} (little-endian search) "
               f"{Color.colorify('likely', 'bold red') if gef.arch.endianness == Endianness.LITTLE_ENDIAN else ''}")
            return

        off = cyclic_pattern.find(pattern_be)
        if off >= 0:
            ok(f"Found at offset {off:d} (big-endian search) "
               f"{Color.colorify('likely', 'bold green') if gef.arch.endianness == Endianness.BIG_ENDIAN else ''}")
            return

        err(f"Pattern '{pattern}' not found")
        return


@register
class HighlightCommand(GenericCommand):
    """Highlight user-defined text matches in GEF output universally."""
    _cmdline_ = "highlight"
    _syntax_ = f"{_cmdline_} (add|remove|list|clear)"
    _aliases_ = ["hl"]

    def __init__(self) -> None:
        super().__init__(prefix=True)
        self["regex"] = (False, "Enable regex highlighting")

    def do_invoke(self, _: List[str]) -> None:
        return self.usage()


@register
class HighlightListCommand(GenericCommand):
    """Show the current highlight table with matches to colors."""
    _cmdline_ = "highlight list"
    _aliases_ = ["highlight ls", "hll"]
    _syntax_ = _cmdline_

    def print_highlight_table(self) -> None:
        if not gef.ui.highlight_table:
            err("no matches found")
            return

        left_pad = max(map(len, gef.ui.highlight_table.keys()))
        for match, color in sorted(gef.ui.highlight_table.items()):
            print(f"{Color.colorify(match.ljust(left_pad), color)} {VERTICAL_LINE} "
                  f"{Color.colorify(color, color)}")
        return

    def do_invoke(self, _: List[str]) -> None:
        return self.print_highlight_table()


@register
class HighlightClearCommand(GenericCommand):
    """Clear the highlight table, remove all matches."""
    _cmdline_ = "highlight clear"
    _aliases_ = ["hlc"]
    _syntax_ = _cmdline_

    def do_invoke(self, _: List[str]) -> None:
        return gef.ui.highlight_table.clear()


@register
class HighlightAddCommand(GenericCommand):
    """Add a match to the highlight table."""
    _cmdline_ = "highlight add"
    _syntax_ = f"{_cmdline_} MATCH COLOR"
    _aliases_ = ["highlight set", "hla"]
    _example_ = f"{_cmdline_} 41414141 yellow"

    def do_invoke(self, argv: List[str]) -> None:
        if len(argv) < 2:
            return self.usage()

        match, color = argv
        gef.ui.highlight_table[match] = color
        return


@register
class HighlightRemoveCommand(GenericCommand):
    """Remove a match in the highlight table."""
    _cmdline_ = "highlight remove"
    _syntax_ = f"{_cmdline_} MATCH"
    _aliases_ = [
        "highlight delete",
        "highlight del",
        "highlight unset",
        "highlight rm",
        "hlr",
    ]
    _example_ = f"{_cmdline_} remove 41414141"

    def do_invoke(self, argv: List[str]) -> None:
        if not argv:
            return self.usage()

        gef.ui.highlight_table.pop(argv[0], None)
        return


#
# GDB Function declaration
#
@deprecated("")
def register_function(cls: Type["GenericFunction"]) -> Type["GenericFunction"]:
    """Decorator for registering a new convenience function to GDB."""
    return cls


class GenericFunction(gdb.Function):
    """This is an abstract class for invoking convenience functions, should not be instantiated."""

    _function_ : str
    _syntax_: str = ""
    _example_ : str = ""

    def __init__(self) -> None:
        super().__init__(self._function_)

    def invoke(self, *args: Any) -> int:
        if not is_alive():
            raise gdb.GdbError("No debugging session active")
        return self.do_invoke(args)

    def arg_to_long(self, args: List, index: int, default: int = 0) -> int:
        try:
            addr = args[index]
            return int(addr) if addr.address is None else int(addr.address)
        except IndexError:
            return default

    def do_invoke(self, args: Any) -> int:
        raise NotImplementedError


@register
class StackOffsetFunction(GenericFunction):
    """Return the current stack base address plus an optional offset."""
    _function_ = "_stack"
    _syntax_   = f"${_function_}()"

    def do_invoke(self, args: List) -> int:
        base = get_section_base_address("[stack]")
        if not base:
            raise gdb.GdbError("Stack not found")

        return self.arg_to_long(args, 0) + base


@register
class HeapBaseFunction(GenericFunction):
    """Return the current heap base address plus an optional offset."""
    _function_ = "_heap"
    _syntax_   = f"${_function_}()"

    def do_invoke(self, args: List) -> int:
        base = gef.heap.base_address
        if not base:
            base = get_section_base_address("[heap]")
            if not base:
                raise gdb.GdbError("Heap not found")
        return self.arg_to_long(args, 0) + base


@register
class SectionBaseFunction(GenericFunction):
    """Return the matching file's base address plus an optional offset.
    Defaults to current file. Note that quotes need to be escaped"""
    _function_ = "_base"
    _syntax_   = "$_base([filepath])"
    _example_  = "p $_base(\\\"/usr/lib/ld-2.33.so\\\")"

    def do_invoke(self, args: List) -> int:
        addr = 0
        try:
            name = args[0].string()
        except IndexError:
            name = gef.session.file.name
        except gdb.error:
            err(f"Invalid arg: {args[0]}")
            return 0

        try:
            base = get_section_base_address(name)
            if base:
                addr = int(base)
        except TypeError:
            err(f"Cannot find section {name}")
            return 0
        return addr


@register
class BssBaseFunction(GenericFunction):
    """Return the current bss base address plus the given offset."""
    _function_ = "_bss"
    _syntax_   = f"${_function_}([OFFSET])"
    _example_ = "deref $_bss(0x20)"

    def do_invoke(self, args: List) -> int:
        base = get_zone_base_address(".bss")
        if not base:
            raise gdb.GdbError("BSS not found")
        return self.arg_to_long(args, 0) + base


@register
class GotBaseFunction(GenericFunction):
    """Return the current GOT base address plus the given offset."""
    _function_ = "_got"
    _syntax_   = f"${_function_}([OFFSET])"
    _example_ = "deref $_got(0x20)"

    def do_invoke(self, args: List) -> int:
        base = get_zone_base_address(".got")
        if not base:
            raise gdb.GdbError("GOT not found")
        return base + self.arg_to_long(args, 0)


@register
class GefFunctionsCommand(GenericCommand):
    """List the convenience functions provided by GEF."""
    _cmdline_ = "functions"
    _syntax_ = _cmdline_

    def __init__(self) -> None:
        super().__init__()
        self.docs = []
        self.should_refresh = True
        return

    def __add__(self, function: GenericFunction):
        """Add function to documentation."""
        doc = getattr(function, "__doc__", "").lstrip()
        if not hasattr(function, "_syntax_"):
            raise ValueError("Function is invalid")
        syntax = getattr(function, "_syntax_").lstrip()
        msg = f"{Color.colorify(syntax, 'bold cyan')}\n {doc}"
        example = getattr(function, "_example_", "").strip()
        if example:
            msg += f"\n {Color.yellowify('Example:')} {example}"
        self.docs.append(msg)
        return self

    def __radd__(self, function: GenericFunction):
        return self.__add__(function)

    def __str__(self) -> str:
        if self.should_refresh:
            self.__rebuild()
        return self.__doc__ or ""

    def __rebuild(self) -> None:
        """Rebuild the documentation for functions."""
        for function in gef.gdb.functions.values():
            self += function

        self.command_size = len(gef.gdb.commands)
        _, cols = get_terminal_size()
        separator = HORIZONTAL_LINE*cols
        self.__doc__ = f"\n{separator}\n".join(sorted(self.docs))
        self.should_refresh = False
        return

    def do_invoke(self, argv) -> None:
        self.dont_repeat()
        gef_print(titlify("GEF - Convenience Functions"))
        gef_print("These functions can be used as arguments to other "
                  "commands to dynamically calculate values\n")
        gef_print(str(self))
        return


#
# GEF internal command classes
#
class GefCommand(gdb.Command):
    """GEF main command: view all new commands by typing `gef`."""

    _cmdline_ = "gef"
    _syntax_  = f"{_cmdline_} (missing|config|save|restore|set|run)"

    def __init__(self) -> None:
        super().__init__(self._cmdline_, gdb.COMMAND_SUPPORT, gdb.COMPLETE_NONE, True)
        gef.config["gef.follow_child"] = GefSetting(True, bool, "Automatically set GDB to follow child when forking")
        gef.config["gef.readline_compat"] = GefSetting(False, bool, "Workaround for readline SOH/ETX issue (SEGV)")
        gef.config["gef.debug"] = GefSetting(False, bool, "Enable debug mode for gef")
        gef.config["gef.autosave_breakpoints_file"] = GefSetting("", str, "Automatically save and restore breakpoints")
        gef.config["gef.extra_plugins_dir"] = GefSetting("", str, "Autoload additional GEF commands from external directory", hooks={"on_write": self.load_extra_plugins})
        gef.config["gef.disable_color"] = GefSetting(False, bool, "Disable all colors in GEF")
        gef.config["gef.tempdir"] = GefSetting(GEF_TEMP_DIR, str, "Directory to use for temporary/cache content")
        gef.config["gef.show_deprecation_warnings"] = GefSetting(True, bool, "Toggle the display of the `deprecated` warnings")

        self.commands : Dict[str, GenericCommand] = collections.OrderedDict()
        self.functions : Dict[str, GenericFunction] = collections.OrderedDict()
        self.missing: Dict[str, Exception] = {}
        return

    @property
    def loaded_commands(self) -> List[Tuple[str, Type[GenericCommand], Any]]:
        print("Obsolete loaded_commands")
        raise

    @property
    def loaded_functions(self) -> List[Type[GenericFunction]]:
        print("Obsolete loaded_functions")
        raise

    @property
    def missing_commands(self) -> Dict[str, Exception]:
        print("Obsolete missing_commands")
        raise

    def setup(self) -> None:
        self.load()

        GefHelpCommand()
        GefConfigCommand()
        GefSaveCommand()
        GefMissingCommand()
        GefSetCommand()
        GefRunCommand()
        GefInstallExtraScriptCommand()

        # restore the settings from config file if any
        GefRestoreCommand()
        return

    def load_extra_plugins(self) -> int:
        def load_plugin(fpath: pathlib.Path) -> bool:
            try:
                dbg(f"Loading '{fpath}'")
                gdb.execute(f"source {fpath}")
            except Exception as e:
                warn(f"Exception while loading {fpath}: {str(e)}")
                return False
            return True

        nb_added = -1
        start_time = time.perf_counter()
        try:
            nb_inital = len(__registered_commands__)
            directories: List[str] = gef.config["gef.extra_plugins_dir"].split(";") or []
            for d in directories:
                d = d.strip()
                if not d: continue
                directory = pathlib.Path(d).expanduser()
                if not directory.is_dir(): continue
                sys.path.append(str(directory.absolute()))
                for entry in directory.iterdir():
                    if entry.is_dir():
                        if entry.name in ('gdb', 'gef', '__pycache__'): continue
                        load_plugin(entry / "__init__.py")
                    else:
                        if entry.suffix != ".py": continue
                        if entry.name == "__init__.py": continue
                        load_plugin(entry)

            nb_added = len(__registered_commands__) - nb_inital
            if nb_added > 0:
                self.load()
                nb_failed = len(__registered_commands__) - len(self.commands)
                end_time = time.perf_counter()
                load_time = end_time - start_time
                ok(f"{Color.colorify(str(nb_added), 'bold green')} extra commands added from "
                   f"'{Color.colorify(', '.join(directories), 'bold blue')}' in {load_time:.2f} seconds")
                if nb_failed != 0:
                    warn(f"{Color.colorify(str(nb_failed), 'bold light_gray')} extra commands/functions failed to be added. "
                    "Check `gef missing` to know why")

        except gdb.error as e:
            err(f"failed: {e}")
        return nb_added

    @property
    def loaded_command_names(self) -> Iterable[str]:
        print("obsolete loaded_command_names")
        return self.commands.keys()

    def invoke(self, args: Any, from_tty: bool) -> None:
        self.dont_repeat()
        gdb.execute("gef help")
        return

    def add_context_pane(self, pane_name: str, display_pane_function: Callable, pane_title_function: Callable, condition: Optional[Callable]) -> None:
        """Add a new context pane to ContextCommand."""
        for _, class_instance in self.commands.items():
            if isinstance(class_instance, ContextCommand):
                context = class_instance
                break
        else:
            err("Cannot find ContextCommand")
            return

        # assure users can toggle the new context
        corrected_settings_name = pane_name.replace(" ", "_")
        gef.config["context.layout"] += f" {corrected_settings_name}"

        # overload the printing of pane title
        context.layout_mapping[corrected_settings_name] = (display_pane_function, pane_title_function, condition)

    def load(self) -> None:
        """Load all the commands and functions defined by GEF into GDB."""
        current_commands = set( self.commands.keys() )
        new_commands = set( [x._cmdline_ for x in __registered_commands__] ) - current_commands
        current_functions = set( self.functions.keys() )
        new_functions = set([x._function_ for x in __registered_functions__]) - current_functions
        self.missing.clear()
        self.__load_time_ms = time.time()* 1000

        # load all new functions
        for name in sorted(new_functions):
            for function_cls in __registered_functions__:
                if function_cls._function_ == name:
                    self.functions[name] = function_cls()
                    break

        # load all new commands
        for name in sorted(new_commands):
            try:
                for command_cls in __registered_commands__:
                    if command_cls._cmdline_ == name:
                        command_instance = command_cls()

                        # create the aliases if any
                        if hasattr(command_instance, "_aliases_"):
                            aliases = getattr(command_instance, "_aliases_")
                            for alias in aliases:
                                GefAlias(alias, name)

                        self.commands[name] = command_instance
                        break

            except Exception as reason:
                self.missing[name] = reason

        self.__load_time_ms = (time.time()* 1000) - self.__load_time_ms
        return


    def show_banner(self) -> None:
        gef_print(f"{Color.greenify('GEF')} for {gef.session.os} ready, "
                  f"type `{Color.colorify('gef', 'underline yellow')}' to start, "
                  f"`{Color.colorify('gef config', 'underline pink')}' to configure")

        ver = f"{sys.version_info.major:d}.{sys.version_info.minor:d}"
        gef_print(f"{Color.colorify(str(len(self.commands)), 'bold green')} commands loaded "
                    f"and {Color.colorify(str(len(self.functions)), 'bold blue')} functions added for "
                    f"GDB {Color.colorify(gdb.VERSION, 'bold yellow')} in {self.__load_time_ms:.2f}ms "
                    f"using Python engine {Color.colorify(ver, 'bold red')}")

        nb_missing = len(self.missing)
        if nb_missing:
                warn(f"{Color.colorify(str(nb_missing), 'bold red')} "
                    f"command{'s' if nb_missing > 1 else ''} could not be loaded, "
                    f"run `{Color.colorify('gef missing', 'underline pink')}` to know why.")
        return


class GefHelpCommand(gdb.Command):
    """GEF help sub-command."""
    _cmdline_ = "gef help"
    _syntax_  = _cmdline_

    def __init__(self) -> None:
        super().__init__(self._cmdline_, gdb.COMMAND_SUPPORT, gdb.COMPLETE_NONE, False)
        self.docs = []
        self.should_refresh = True
        self.command_size = 0
        return

    def invoke(self, args: Any, from_tty: bool) -> None:
        self.dont_repeat()
        gef_print(titlify("GEF - GDB Enhanced Features"))
        gef_print(str(self))
        return

    def __rebuild(self) -> None:
        """Rebuild the documentation."""
        for name, cmd in gef.gdb.commands.items():
            self += (name, cmd)

        self.command_size = len(gef.gdb.commands)
        _, cols = get_terminal_size()
        separator = HORIZONTAL_LINE*cols
        self.__doc__ = f"\n{separator}\n".join(sorted(self.docs))
        self.should_refresh = False
        return

    def __add__(self, command: Tuple[str, GenericCommand]):
        """Add command to GEF documentation."""
        cmd, class_obj = command
        if " " in cmd:
            # do not print subcommands in gef help
            return self
        doc = getattr(class_obj, "__doc__", "").lstrip()
        aliases = f"Aliases: {', '.join(class_obj._aliases_)}" if hasattr(class_obj, "_aliases_") else ""
        msg = f"{Color.colorify(cmd, 'bold red')}\n{doc}\n{aliases}"
        self.docs.append(msg)
        return self

    def __radd__(self, command: Tuple[str, GenericCommand]):
        return self.__add__(command)

    def __str__(self) -> str:
        """Lazily regenerate the `gef help` object if it was modified"""
        # quick check in case the docs have changed
        if self.should_refresh or self.command_size != len(gef.gdb.commands):
            self.__rebuild()
        return self.__doc__ or ""


class GefConfigCommand(gdb.Command):
    """GEF configuration sub-command
    This command will help set/view GEF settings for the current debugging session.
    It is possible to make those changes permanent by running `gef save` (refer
    to this command help), and/or restore previously saved settings by running
    `gef restore` (refer help).
    """
    _cmdline_ = "gef config"
    _syntax_  = f"{_cmdline_} [setting_name] [setting_value]"

    def __init__(self) -> None:
        super().__init__(self._cmdline_, gdb.COMMAND_NONE, prefix=False)
        return

    def invoke(self, args: str, from_tty: bool) -> None:
        self.dont_repeat()
        argv = gdb.string_to_argv(args)
        argc = len(argv)

        if not (0 <= argc <= 2):
            err("Invalid number of arguments")
            return

        if argc == 0:
            gef_print(titlify("GEF configuration settings"))
            self.print_settings()
            return

        if argc == 1:
            prefix = argv[0]
            names = [x for x in gef.config.keys() if x.startswith(prefix)]
            if names:
                if len(names) == 1:
                    gef_print(titlify(f"GEF configuration setting: {names[0]}"))
                    self.print_setting(names[0], verbose=True)
                else:
                    gef_print(titlify(f"GEF configuration settings matching '{argv[0]}'"))
                    for name in names: self.print_setting(name)
            return

        self.set_setting(argv)
        return

    def print_setting(self, plugin_name: str, verbose: bool = False) -> None:
        res = gef.config.raw_entry(plugin_name)
        string_color = gef.config["theme.dereference_string"]
        misc_color = gef.config["theme.dereference_base_address"]

        if not res:
            return

        _setting = Color.colorify(plugin_name, "green")
        _type = res.type.__name__
        if _type == "str":
            _value = f'"{Color.colorify(res.value, string_color)}"'
        else:
            _value = Color.colorify(res.value, misc_color)

        gef_print(f"{_setting} ({_type}) = {_value}")

        if verbose:
            gef_print(Color.colorify("\nDescription:", "bold underline"))
            gef_print(f"\t{res.description}")
        return

    def print_settings(self) -> None:
        for x in sorted(gef.config):
            self.print_setting(x)
        return

    def set_setting(self, argv: Tuple[str, Any]) -> None:
        global gef
        key, new_value = argv

        if "." not in key:
            err("Invalid command format")
            return

        loaded_commands = list( gef.gdb.commands.keys()) + ["gef"]
        plugin_name = key.split(".", 1)[0]
        if plugin_name not in loaded_commands:
            err(f"Unknown plugin '{plugin_name}'")
            return

        if key not in gef.config:
            err(f"'{key}' is not a valid configuration setting")
            return

        _type = gef.config.raw_entry(key).type
        try:
            if _type == bool:
                _newval = True if new_value.upper() in ("TRUE", "T", "1") else False
            else:
                _newval = new_value

            gef.config[key] = _newval
        except Exception as e:
            err(f"'{key}' expects type '{_type.__name__}', got {type(new_value).__name__}: reason {str(e)}")
            return

        reset_all_caches()
        return

    def complete(self, text: str, word: str) -> List[str]:
        settings = sorted(gef.config)

        if text == "":
            # no prefix: example: `gef config TAB`
            return [s for s in settings if word in s]

        if "." not in text:
            # if looking for possible prefix
            return [s for s in settings if s.startswith(text.strip())]

        # finally, look for possible values for given prefix
        return [s.split(".", 1)[1] for s in settings if s.startswith(text.strip())]


class GefSaveCommand(gdb.Command):
    """GEF save sub-command.
    Saves the current configuration of GEF to disk (by default in file '~/.gef.rc')."""
    _cmdline_ = "gef save"
    _syntax_  = _cmdline_

    def __init__(self) -> None:
        super().__init__(self._cmdline_, gdb.COMMAND_SUPPORT, gdb.COMPLETE_NONE, False)
        return

    def invoke(self, args: Any, from_tty: bool) -> None:
        self.dont_repeat()
        cfg = configparser.RawConfigParser()
        old_sect = None

        # save the configuration
        for key in sorted(gef.config):
            sect, optname = key.split(".", 1)
            value = gef.config[key]

            if old_sect != sect:
                cfg.add_section(sect)
                old_sect = sect

            cfg.set(sect, optname, value)

        # save the aliases
        cfg.add_section("aliases")
        for alias in gef.session.aliases:
            cfg.set("aliases", alias._alias, alias._command)

        with GEF_RC.open("w") as fd:
            cfg.write(fd)

        ok(f"Configuration saved to '{GEF_RC}'")
        return


class GefRestoreCommand(gdb.Command):
    """GEF restore sub-command.
    Loads settings from file '~/.gef.rc' and apply them to the configuration of GEF."""
    _cmdline_ = "gef restore"
    _syntax_  = _cmdline_

    def __init__(self) -> None:
        super().__init__(self._cmdline_, gdb.COMMAND_SUPPORT, gdb.COMPLETE_NONE, False)
        self.reload(True)
        return

    def invoke(self, args: str, from_tty: bool) -> None:
        self.dont_repeat()
        if  GEF_RC.is_file():
            quiet = (args.lower() == "quiet")
            self.reload(quiet)
        return

    def reload(self, quiet: bool):
        cfg = configparser.ConfigParser()
        cfg.read(GEF_RC)

        for section in cfg.sections():
            if section == "aliases":
                # load the aliases
                for key in cfg.options(section):
                    try:
                        GefAlias(key, cfg.get(section, key))
                    except:
                        pass
                continue

            # load the other options
            for optname in cfg.options(section):
                key = f"{section}.{optname}"
                try:
                    setting = gef.config.raw_entry(key)
                except Exception:
                    continue
                new_value = cfg.get(section, optname)
                if setting.type == bool:
                    new_value = True if new_value.upper() in ("TRUE", "T", "1") else False
                setting.value = setting.type(new_value)

        if not quiet:
            ok(f"Configuration from '{Color.colorify(str(GEF_RC), 'bold blue')}' restored")
        return


class GefMissingCommand(gdb.Command):
    """GEF missing sub-command
    Display the GEF commands that could not be loaded, along with the reason of why
    they could not be loaded.
    """
    _cmdline_ = "gef missing"
    _syntax_  = _cmdline_

    def __init__(self) -> None:
        super().__init__(self._cmdline_, gdb.COMMAND_SUPPORT, gdb.COMPLETE_NONE, False)
        return

    def invoke(self, args: Any, from_tty: bool) -> None:
        self.dont_repeat()
        missing_commands = gef.gdb.missing
        if not missing_commands:
            ok("No missing command")
            return

        for missing_command, reason in missing_commands.items():
            warn(f"Command `{missing_command}` is missing, reason {RIGHT_ARROW} {reason}")
        return


class GefSetCommand(gdb.Command):
    """Override GDB set commands with the context from GEF."""
    _cmdline_ = "gef set"
    _syntax_  = f"{_cmdline_} [GDB_SET_ARGUMENTS]"

    def __init__(self) -> None:
        super().__init__(self._cmdline_, gdb.COMMAND_SUPPORT, gdb.COMPLETE_SYMBOL, False)
        return

    def invoke(self, args: Any, from_tty: bool) -> None:
        self.dont_repeat()
        args = args.split()
        cmd = ["set", args[0],]
        for p in args[1:]:
            if p.startswith("$_gef"):
                c = gdb.parse_and_eval(p)
                cmd.append(c.string())
            else:
                cmd.append(p)

        gdb.execute(" ".join(cmd))
        return


class GefRunCommand(gdb.Command):
    """Override GDB run commands with the context from GEF.
    Simple wrapper for GDB run command to use arguments set from `gef set args`."""
    _cmdline_ = "gef run"
    _syntax_  = f"{_cmdline_} [GDB_RUN_ARGUMENTS]"

    def __init__(self) -> None:
        super().__init__(self._cmdline_, gdb.COMMAND_SUPPORT, gdb.COMPLETE_FILENAME, False)
        return

    def invoke(self, args: Any, from_tty: bool) -> None:
        self.dont_repeat()
        if is_alive():
            gdb.execute("continue")
            return

        argv = args.split()
        gdb.execute(f"gef set args {' '.join(argv)}")
        gdb.execute("run")
        return


class GefAlias(gdb.Command):
    """Simple aliasing wrapper because GDB doesn't do what it should."""

    def __init__(self, alias: str, command: str, completer_class: int = gdb.COMPLETE_NONE, command_class: int = gdb.COMMAND_NONE) -> None:
        p = command.split()
        if not p:
            return

        if any(x for x in gef.session.aliases if x._alias == alias):
            return

        self._command = command
        self._alias = alias
        c = command.split()[0]
        r = self.lookup_command(c)
        self.__doc__ = f"Alias for '{Color.greenify(command)}'"
        if r is not None:
            _instance = r[1]
            self.__doc__ += f": {_instance.__doc__}"

            if hasattr(_instance,  "complete"):
                self.complete = _instance.complete

        super().__init__(alias, command_class, completer_class=completer_class)
        gef.session.aliases.append(self)
        return

    def invoke(self, args: Any, from_tty: bool) -> None:
        gdb.execute(f"{self._command} {args}", from_tty=from_tty)
        return

    def lookup_command(self, cmd: str) -> Optional[Tuple[str, GenericCommand]]:
        global gef
        for _name, _instance in gef.gdb.commands.items():
            if cmd == _name:
                return _name, _instance

        return None


@register
class AliasesCommand(GenericCommand):
    """Base command to add, remove, or list aliases."""

    _cmdline_ = "aliases"
    _syntax_  = f"{_cmdline_} (add|rm|ls)"

    def __init__(self) -> None:
        super().__init__(prefix=True)
        return

    def do_invoke(self, _: List[str]) -> None:
        self.usage()
        return


@register
class AliasesAddCommand(AliasesCommand):
    """Command to add aliases."""

    _cmdline_ = "aliases add"
    _syntax_  = f"{_cmdline_} [ALIAS] [COMMAND]"
    _example_ = f"{_cmdline_} scope telescope"

    def __init__(self) -> None:
        super().__init__()
        return

    def do_invoke(self, argv: List[str]) -> None:
        if len(argv) < 2:
            self.usage()
            return
        GefAlias(argv[0], " ".join(argv[1:]))
        return


@register
class AliasesRmCommand(AliasesCommand):
    """Command to remove aliases."""

    _cmdline_ = "aliases rm"
    _syntax_ = f"{_cmdline_} [ALIAS]"

    def __init__(self) -> None:
        super().__init__()
        return

    def do_invoke(self, argv: List[str]) -> None:
        global gef
        if len(argv) != 1:
            self.usage()
            return
        try:
            alias_to_remove = next(filter(lambda x: x._alias == argv[0], gef.session.aliases))
            gef.session.aliases.remove(alias_to_remove)
        except (ValueError, StopIteration):
            err(f"{argv[0]} not found in aliases.")
            return
        gef_print("You must reload GEF for alias removals to apply.")
        return


@register
class AliasesListCommand(AliasesCommand):
    """Command to list aliases."""

    _cmdline_ = "aliases ls"
    _syntax_ = _cmdline_

    def __init__(self) -> None:
        super().__init__()
        return

    def do_invoke(self, _: List[str]) -> None:
        ok("Aliases defined:")
        for a in gef.session.aliases:
            gef_print(f"{a._alias:30s} {RIGHT_ARROW} {a._command}")
        return


class GefTmuxSetup(gdb.Command):
    """Setup a confortable tmux debugging environment."""

    def __init__(self) -> None:
        super().__init__("tmux-setup", gdb.COMMAND_NONE, gdb.COMPLETE_NONE)
        GefAlias("screen-setup", "tmux-setup")
        return

    def invoke(self, args: Any, from_tty: bool) -> None:
        self.dont_repeat()

        tmux = os.getenv("TMUX")
        if tmux:
            self.tmux_setup()
            return

        screen = os.getenv("TERM")
        if screen is not None and screen == "screen":
            self.screen_setup()
            return

        warn("Not in a tmux/screen session")
        return

    def tmux_setup(self) -> None:
        """Prepare the tmux environment by vertically splitting the current pane, and
        forcing the context to be redirected there."""
        tmux = which("tmux")
        ok("tmux session found, splitting window...")
        old_ptses = set(os.listdir("/dev/pts"))
        gdb.execute(f"! {tmux} split-window -h 'clear ; cat'")
        gdb.execute(f"! {tmux} select-pane -L")
        new_ptses = set(os.listdir("/dev/pts"))
        pty = list(new_ptses - old_ptses)[0]
        pty = f"/dev/pts/{pty}"
        ok(f"Setting `context.redirect` to '{pty}'...")
        gdb.execute(f"gef config context.redirect {pty}")
        ok("Done!")
        return

    def screen_setup(self) -> None:
        """Hackish equivalent of the tmux_setup() function for screen."""
        screen = which("screen")
        sty = os.getenv("STY")
        ok("screen session found, splitting window...")
        fd_script, script_path = tempfile.mkstemp()
        fd_tty, tty_path = tempfile.mkstemp()
        os.close(fd_tty)

        with os.fdopen(fd_script, "w") as f:
            f.write("startup_message off\n")
            f.write("split -v\n")
            f.write("focus right\n")
            f.write(f"screen bash -c 'tty > {tty_path}; clear; cat'\n")
            f.write("focus left\n")

        gdb.execute(f"! {screen} -r {sty} -m -d -X source {script_path}")
        # artificial delay to make sure `tty_path` is populated
        time.sleep(0.25)
        with open(tty_path, "r") as f:
            pty = f.read().strip()
        ok(f"Setting `context.redirect` to '{pty}'...")
        gdb.execute(f"gef config context.redirect {pty}")
        ok("Done!")
        os.unlink(script_path)
        os.unlink(tty_path)
        return


class GefInstallExtraScriptCommand(gdb.Command):
    """`gef install` command: installs one or more scripts from the `gef-extras` script repo. Note that the command
    doesn't check for external dependencies the script(s) might require."""
    _cmdline_ = "gef install"
    _syntax_  = f"{_cmdline_} SCRIPTNAME [SCRIPTNAME [SCRIPTNAME...]]"

    def __init__(self) -> None:
        super().__init__(self._cmdline_, gdb.COMMAND_SUPPORT, gdb.COMPLETE_NONE, False)
        self.branch = gef.config.get("gef.extras_default_branch", GEF_EXTRAS_DEFAULT_BRANCH)
        return

    def invoke(self, argv: str, from_tty: bool) -> None:
        self.dont_repeat()
        if not argv:
            err("No script name provided")
            return

        args = argv.split()

        if "--list" in args or "-l" in args:
            subprocess.run(["xdg-open", f"https://github.com/hugsy/gef-extras/{self.branch}/"])
            return

        self.dirpath = pathlib.Path(gef.config["gef.tempdir"]).expanduser().absolute()
        if not self.dirpath.is_dir():
            err("'gef.tempdir' is not a valid directory")
            return

        for script in args:
            script = script.lower()
            if not self.__install_extras_script(script):
                warn(f"Failed to install '{script}', skipping...")
        return


    def __install_extras_script(self, script: str) -> bool:
        fpath = self.dirpath / f"{script}.py"
        if not fpath.exists():
            url = f"https://raw.githubusercontent.com/hugsy/gef-extras/{self.branch}/scripts/{script}.py"
            info(f"Searching for '{script}.py' in `gef-extras@{self.branch}`...")
            data = http_get(url)
            if not data:
                warn("Not found")
                return False

            with fpath.open("wb") as fd:
                fd.write(data)
                fd.flush()

        old_command_set = set(gef.gdb.commands)
        gdb.execute(f"source {fpath}")
        new_command_set = set(gef.gdb.commands)
        new_commands = [f"`{c[0]}`" for c in (new_command_set - old_command_set)]
        ok(f"Installed file '{fpath}', new command(s) available: {', '.join(new_commands)}")
        return True


#
# GEF internal  classes
#

def __gef_prompt__(current_prompt: Callable[[Callable], str]) -> str:
    """GEF custom prompt function."""
    if gef.config["gef.readline_compat"] is True: return GEF_PROMPT
    if gef.config["gef.disable_color"] is True: return GEF_PROMPT
    prompt = ""
    if gef.session.remote:
        prompt += Color.boldify("(remote) ")
    prompt += GEF_PROMPT_ON if is_alive() else GEF_PROMPT_OFF
    return prompt


class GefManager(metaclass=abc.ABCMeta):
    def reset_caches(self) -> None:
        """Reset the LRU-cached attributes"""
        for attr in dir(self):
            try:
                obj = getattr(self, attr)
                if not hasattr(obj, "cache_clear"):
                    continue
                obj.cache_clear()
            except: # we're reseting the cache here, we don't care if (or which) exception triggers
                continue
        return


class GefMemoryManager(GefManager):
    """Class that manages memory access for gef."""
    def __init__(self) -> None:
        self.reset_caches()
        return

    def reset_caches(self) -> None:
        super().reset_caches()
        self.__maps = None
        return

    def write(self, address: int, buffer: ByteString, length: int = 0x10) -> None:
        """Write `buffer` at address `address`."""
        gdb.selected_inferior().write_memory(address, buffer, length)

    def read(self, addr: int, length: int = 0x10) -> bytes:
        """Return a `length` long byte array with the copy of the process memory at `addr`."""
        return gdb.selected_inferior().read_memory(addr, length).tobytes()

    def read_integer(self, addr: int) -> int:
        """Return an integer read from memory."""
        sz = gef.arch.ptrsize
        mem = self.read(addr, sz)
        unpack = u32 if sz == 4 else u64
        return unpack(mem)

    def read_cstring(self,
                     address: int,
                     max_length: int = GEF_MAX_STRING_LENGTH,
                     encoding: Optional[str] = None) -> str:
        """Return a C-string read from memory."""
        encoding = encoding or "unicode-escape"
        length = min(address | (DEFAULT_PAGE_SIZE-1), max_length+1)

        try:
            res_bytes = self.read(address, length)
        except gdb.error:
            err(f"Can't read memory at '{address}'")
            return ""
        try:
            with warnings.catch_warnings():
                # ignore DeprecationWarnings (see #735)
                warnings.simplefilter("ignore")
                res = res_bytes.decode(encoding, "strict")
        except UnicodeDecodeError:
            # latin-1 as fallback due to its single-byte to glyph mapping
            res = res_bytes.decode("latin-1", "replace")

        res = res.split("\x00", 1)[0]
        ustr = res.replace("\n", "\\n").replace("\r", "\\r").replace("\t", "\\t")
        if max_length and len(res) > max_length:
            return f"{ustr[:max_length]}[...]"
        return ustr

    def read_ascii_string(self, address: int) -> Optional[str]:
        """Read an ASCII string from memory"""
        cstr = self.read_cstring(address)
        if isinstance(cstr, str) and cstr and all(x in string.printable for x in cstr):
            return cstr
        return None

    @property
    def maps(self) -> List[Section]:
        if not self.__maps:
            x = Permission.EXECUTE
            rw = Permission.READ | Permission.WRITE
            rx = Permission.READ | Permission.EXECUTE
            rwx = Permission.READ | Permission.WRITE | Permission.EXECUTE

            self.__maps = []
            self.__maps += [Section(name="BIOS", start=0x00000000, end=0x00004000, permission=x)]
            self.__maps += [Section(name="EWRAM", start=0x02000000, end=0x02040000, permission=rwx)]
            self.__maps += [Section(name="IWRAM", start=0x03000000, end=0x03008000, permission=rwx)]
            self.__maps += [Section(name="IO", start=0x04000000, end=0x040003ff, permission=rw)]
            self.__maps += [Section(name="PAL", start=0x05000000, end=0x05000400, permission=rwx)]
            self.__maps += [Section(name="VRAM", start=0x06000000, end=0x06018000, permission=rwx)]
            self.__maps += [Section(name="OAM", start=0x07000000, end=0x07000400, permission=rwx)]
            self.__maps += [Section(name="ROM0", start=0x08000000, end=0x0a000000, permission=rx)]
            self.__maps += [Section(name="ROM1", start=0x0a000000, end=0x0c000000, permission=rx)]
            self.__maps += [Section(name="ROM2", start=0x0c000000, end=0x0e000000, permission=rx)]
            self.__maps += [Section(name="SRAM", start=0x0e000000, end=0x0e010000, permission=rwx)]
        return self.__maps


class GefSetting:
    """Basic class for storing gef settings as objects"""
    READ_ACCESS = 0
    WRITE_ACCESS = 1

    def __init__(self, value: Any, cls: Optional[type] = None, description: Optional[str] = None, hooks: Optional[Dict[str, Callable]] = None)  -> None:
        self.value = value
        self.type = cls or type(value)
        self.description = description or ""
        self.hooks: Tuple[List[Callable], List[Callable]] = ([], [])
        if hooks:
            for access, func in hooks.items():
                if access == "on_read":
                    idx = GefSetting.READ_ACCESS
                elif access == "on_write":
                    idx = GefSetting.WRITE_ACCESS
                else:
                    raise ValueError
                if not callable(func):
                    raise ValueError(f"hook is not callable")
                self.hooks[idx].append(func)
        return

    def __str__(self) -> str:
        return f"Setting(type={self.type.__name__}, value='{self.value}', desc='{self.description[:10]}...', "\
            f"read_hooks={len(self.hooks[GefSetting.READ_ACCESS])}, write_hooks={len(self.hooks[GefSetting.READ_ACCESS])})"


class GefSettingsManager(dict):
    """
    GefSettings acts as a dict where the global settings are stored and can be read, written or deleted as any other dict.
    For instance, to read a specific command setting: `gef.config[mycommand.mysetting]`
    """
    def __getitem__(self, name: str) -> Any:
        setting : GefSetting = super().__getitem__(name)
        self.__invoke_read_hooks(setting)
        return setting.value

    def __setitem__(self, name: str, value: Any) -> None:
        # check if the key exists
        if super().__contains__(name):
            # if so, update its value directly
            setting = super().__getitem__(name)
            if not isinstance(setting, GefSetting): raise ValueError
            setting.value = setting.type(value)
        else:
            # if not, `value` must be a GefSetting
            if not isinstance(value, GefSetting): raise Exception("Invalid argument")
            if not value.type: raise Exception("Invalid type")
            if not value.description: raise Exception("Invalid description")
            setting = value
        super().__setitem__(name, setting)
        self.__invoke_write_hooks(setting)
        return

    def __delitem__(self, name: str) -> None:
        super().__delitem__(name)
        return

    def raw_entry(self, name: str) -> GefSetting:
        return super().__getitem__(name)

    def __invoke_read_hooks(self, setting: GefSetting) -> None:
        self.__invoke_hooks(is_write=False, setting=setting)
        return

    def __invoke_write_hooks(self, setting: GefSetting) -> None:
        self.__invoke_hooks(is_write=True, setting=setting)
        return

    def __invoke_hooks(self, is_write: bool, setting: GefSetting) -> None:
        if not setting.hooks:
            return
        idx = int(is_write)
        if setting.hooks[idx]:
            for callback in setting.hooks[idx]:
                callback()
        return


class GefSessionManager(GefManager):
    """Class managing the runtime properties of GEF. """
    def __init__(self) -> None:
        self.reset_caches()
        self.remote: Optional["GefRemoteSessionManager"] = None
        self.qemu_mode: bool = False
        self.convenience_vars_index: int = 0
        self.pie_breakpoints: Dict[int, PieVirtualBreakpoint] = {}
        self.pie_counter: int = 1
        self.aliases: List[GefAlias] = []
        self.modules: List[FileFormat] = []
        self.constants = {} # a dict for runtime constants (like 3rd party file paths)
        for constant in ("python3", "readelf", "file", "ps"):
            self.constants[constant] = which(constant)
        return

    def reset_caches(self) -> None:
        super().reset_caches()
        self._auxiliary_vector = None
        self._pagesize = None
        self._os = None
        self._pid = None
        self._file = None
        self._canary = None
        self._maps: Optional[pathlib.Path] = None
        return

    def __str__(self) -> str:
        return f"Session({'Local' if self.remote is None else 'Remote'}, pid={self.pid or 'Not running'}, os='{self.os}')"

    @property
    def auxiliary_vector(self) -> Optional[Dict[str, int]]:
        if not is_alive():
            return None

        if not self._auxiliary_vector:
            auxiliary_vector = {}
            auxv_info = gdb.execute("info auxv", to_string=True)
            if "failed" in auxv_info:
                err(auxv_info)
                return None
            for line in auxv_info.splitlines():
                line = line.split('"')[0].strip()  # remove the ending string (if any)
                line = line.split()  # split the string by whitespace(s)
                if len(line) < 4:
                    continue
                __av_type = line[1]
                __av_value = line[-1]
                auxiliary_vector[__av_type] = int(__av_value, base=0)
            self._auxiliary_vector = auxiliary_vector
        return self._auxiliary_vector

    @property
    def os(self) -> str:
        """Return the current OS."""
        if not self._os:
            self._os = platform.system().lower()
        return self._os

    @property
    def pid(self) -> int:
        """Return the PID of the target process."""
        if not self._pid:
            pid = gdb.selected_inferior().pid if not gef.session.qemu_mode else gdb.selected_thread().ptid[1]
            if not pid:
                raise RuntimeError("cannot retrieve PID for target process")
            self._pid = pid
        return self._pid

    @property
    def file(self) -> Optional[pathlib.Path]:
        """Return a Path object of the target process."""
        if gef.session.remote is not None:
            return gef.session.remote.file
        fpath: str = gdb.current_progspace().filename
        if fpath and not self._file:
            self._file = pathlib.Path(fpath).expanduser()
        return self._file

    @property
    def cwd(self) -> Optional[pathlib.Path]:
        if gef.session.remote is not None:
            return gef.session.remote.root
        return self.file.parent if self.file else None

    @property
    def pagesize(self) -> int:
        """Get the system page size"""
        auxval = self.auxiliary_vector
        if not auxval:
            return DEFAULT_PAGE_SIZE
        self._pagesize = auxval["AT_PAGESZ"]
        return self._pagesize

    @property
    def canary(self) -> Optional[Tuple[int, int]]:
        """Returns a tuple of the canary address and value, read from the auxiliary vector."""
        auxval = self.auxiliary_vector
        if not auxval:
            return None
        canary_location = auxval["AT_RANDOM"]
        canary = gef.memory.read_integer(canary_location)
        canary &= ~0xFF
        self._canary = (canary, canary_location)
        return self._canary

    @property
    def maps(self) -> Optional[pathlib.Path]:
        """Returns the Path to the procfs entry for the memory mapping."""
        if not is_alive():
            return None
        if not self._maps:
            if gef.session.remote is not None:
                self._maps = gef.session.remote.maps
            else:
                self._maps = pathlib.Path(f"/proc/{self.pid}/maps")
        return self._maps


class GefRemoteSessionManager(GefSessionManager):
    """Class for managing remote sessions with GEF. It will create a temporary environment
    designed to clone the remote one."""
    def __init__(self, host: str, port: int, pid: int =-1, qemu: Optional[pathlib.Path] = None) -> None:
        super().__init__()
        self.__host = host
        self.__port = port
        self.__local_root_fd = tempfile.TemporaryDirectory()
        self.__local_root_path = pathlib.Path(self.__local_root_fd.name)
        self.__qemu = qemu
        dbg(f"[remote] initializing remote session with {self.target} under {self.root}")
        if not self.connect(pid):
            raise EnvironmentError(f"Cannot connect to remote target {self.target}")
        if not self.setup():
            raise EnvironmentError(f"Failed to create a proper environment for {self.target}")
        return

    def __del__(self) -> None:
        self.__local_root_fd.cleanup()
        try:
            gef_on_new_unhook(self.remote_objfile_event_handler)
            gef_on_new_hook(new_objfile_handler)
        except Exception as e:
            warn(f"Exception while restoring local context: {str(e)}")
        return

    def in_qemu_user(self) -> bool:
        return self.__qemu is not None

    def __str__(self) -> str:
        return f"RemoteSession(target='{self.target}', local='{self.root}', pid={self.pid}, qemu_user={bool(self.in_qemu_user())})"

    @property
    def target(self) -> str:
        return f"{self.__host}:{self.__port}"

    @property
    def root(self) -> pathlib.Path:
        return self.__local_root_path.absolute()

    @property
    def file(self) -> pathlib.Path:
        """Path to the file being debugged as seen by the remote endpoint."""
        if not self._file:
            filename = gdb.current_progspace().filename
            if not filename:
                raise RuntimeError("No session started")
            start_idx = len("target:") if filename.startswith("target:") else 0
            self._file = pathlib.Path(filename[start_idx:])
        return self._file

    @property
    def lfile(self) -> pathlib.Path:
        """Local path to the file being debugged."""
        return self.root / str(self.file).lstrip("/")

    @property
    def maps(self) -> pathlib.Path:
        if not self._maps:
            self._maps = self.root / f"proc/{self.pid}/maps"
        return self._maps

    def sync(self, src: str, dst: Optional[str] = None) -> bool:
        """Copy the `src` into the temporary chroot. If `dst` is provided, that path will be
        used instead of `src`."""
        if not dst:
            dst = src
        tgt = self.root / dst.lstrip("/")
        if tgt.exists():
            return True
        tgt.parent.mkdir(parents=True, exist_ok=True)
        dbg(f"[remote] downloading '{src}' -> '{tgt}'")
        gdb.execute(f"remote get {src} {tgt.absolute()}")
        return tgt.exists()

    def connect(self, pid: int) -> bool:
        """Connect to remote target. If in extended mode, also attach to the given PID."""
        # before anything, register our new hook to download files from the remote target
        dbg(f"[remote] Installing new objfile handlers")
        gef_on_new_unhook(new_objfile_handler)
        gef_on_new_hook(self.remote_objfile_event_handler)

        # then attempt to connect
        is_extended_mode = (pid > -1)
        dbg(f"[remote] Enabling extended remote: {bool(is_extended_mode)}")
        try:
            with DisableContextOutputContext():
                cmd = f"target {'extended-' if is_extended_mode else ''}remote {self.target}"
                dbg(f"[remote] Executing '{cmd}'")
                gdb.execute(cmd)
                if is_extended_mode:
                    gdb.execute(f"attach {pid:d}")
            return True
        except Exception as e:
            err(f"Failed to connect to {self.target}: {e}")

        # a failure will trigger the cleanup, deleting our hook anyway
        return False

    def setup(self) -> bool:
        # setup remote adequately depending on remote or qemu mode
        if self.in_qemu_user():
            dbg(f"Setting up as qemu session, target={self.__qemu}")
            self.__setup_qemu()
        else:
            dbg(f"Setting up as remote session")
            self.__setup_remote()

        # refresh gef to consider the binary
        reset_all_caches()
        gef.binary = Elf(self.lfile)
        reset_architecture()
        return True

    def __setup_qemu(self) -> bool:
        # setup emulated file in the chroot
        assert self.__qemu
        target = self.root / str(self.__qemu.parent).lstrip("/")
        target.mkdir(parents=True, exist_ok=False)
        shutil.copy2(self.__qemu, target)
        self._file = self.__qemu
        assert self.lfile.exists()

        # create a procfs
        procfs = self.root / f"proc/{self.pid}/"
        procfs.mkdir(parents=True, exist_ok=True)

        ## /proc/pid/cmdline
        cmdline = procfs / "cmdline"
        if not cmdline.exists():
            with cmdline.open("w") as fd:
                fd.write("")

        ## /proc/pid/environ
        environ = procfs / "environ"
        if not environ.exists():
            with environ.open("wb") as fd:
                fd.write(b"PATH=/bin\x00HOME=/tmp\x00")

        ## /proc/pid/maps
        maps = procfs / "maps"
        if not maps.exists():
            with maps.open("w") as fd:
                fname = self.file.absolute()
                mem_range = "00000000-ffffffff" if is_32bit() else "0000000000000000-ffffffffffffffff"
                fd.write(f"{mem_range} rwxp 00000000 00:00 0                    {fname}\n")
        return True

    def __setup_remote(self) -> bool:
        # get the file
        fpath = f"/proc/{self.pid}/exe"
        if not self.sync(fpath, str(self.file)):
            err(f"'{fpath}' could not be fetched on the remote system.")
            return False

        # pseudo procfs
        for _file in ("maps", "environ", "cmdline"):
            fpath = f"/proc/{self.pid}/{_file}"
            if not self.sync(fpath):
                err(f"'{fpath}' could not be fetched on the remote system.")
                return False

        # makeup a fake mem mapping in case we failed to retrieve it
        maps = self.root / f"proc/{self.pid}/maps"
        if not maps.exists():
            with maps.open("w") as fd:
                fname = self.file.absolute()
                mem_range = "00000000-ffffffff" if is_32bit() else "0000000000000000-ffffffffffffffff"
                fd.write(f"{mem_range} rwxp 00000000 00:00 0                    {fname}\n")
        return True

    def remote_objfile_event_handler(self, evt: "gdb.NewObjFileEvent") -> None:
        dbg(f"[remote] in remote_objfile_handler({evt.new_objfile.filename if evt else 'None'}))")
        if not evt:
            return
        if not evt.new_objfile.filename.startswith("target:") and not evt.new_objfile.filename.startswith("/"):
            warn(f"[remote] skipping '{evt.new_objfile.filename}'")
            return
        if evt.new_objfile.filename.startswith("target:"):
            src: str = evt.new_objfile.filename[len("target:"):]
            if not self.sync(src):
                raise FileNotFoundError(f"Failed to sync '{src}'")
        return


class GefUiManager(GefManager):
    """Class managing UI settings."""
    def __init__(self) -> None:
        self.redirect_fd : Optional[TextIOWrapper] = None
        self.context_hidden = False
        self.stream_buffer : Optional[StringIO] = None
        self.highlight_table: Dict[str, str] = {}
        self.watches: Dict[int, Tuple[int, str]] = {}
        self.context_messages: List[Tuple[str, str]] = []
        return


class Gef:
    """The GEF root class, which serves as a entrypoint for all the debugging session attributes (architecture,
    memory, settings, etc.)."""
    binary: Optional[FileFormat]
    arch: Architecture
    config : GefSettingsManager
    ui: GefUiManager
    memory : GefMemoryManager
    session : GefSessionManager
    gdb: GefCommand

    def __init__(self) -> None:
        self.binary: Optional[FileFormat] = None
        self.arch: Architecture = GenericArchitecture() # see PR #516, will be reset by `new_objfile_handler`
        self.config = GefSettingsManager()
        self.ui = GefUiManager()
        return

    def __str__(self) -> str:
        return f"Gef(binary='{self.binary or 'None'}', arch={self.arch})"

    def reinitialize_managers(self) -> None:
        """Reinitialize the managers. Avoid calling this function directly, using `pi reset()` is preferred"""
        self.memory = GefMemoryManager()
        self.session = GefSessionManager()
        return

    def setup(self) -> None:
        """Setup initialize the runtime setup, which may require for the `gef` to be not None."""
        self.reinitialize_managers()
        self.gdb = GefCommand()
        self.gdb.setup()
        tempdir = self.config["gef.tempdir"]
        gef_makedirs(tempdir)
        gdb.execute(f"save gdb-index {tempdir}")
        return

    def reset_caches(self) -> None:
        """Recursively clean the cache of all the managers. Avoid calling this function directly, using `reset-cache`
        is preferred"""
        for mgr in (self.memory, self.session, self.arch):
            mgr.reset_caches()
        return


if __name__ == "__main__":
    if sys.version_info[0] == 2:
        err("GEF has dropped Python2 support for GDB when it reached EOL on 2020/01/01.")
        err("If you require GEF for GDB+Python2, use https://github.com/hugsy/gef-legacy.")
        exit(1)

    if GDB_VERSION < GDB_MIN_VERSION or PYTHON_VERSION < PYTHON_MIN_VERSION:
        err("You're using an old version of GDB. GEF will not work correctly. "
            f"Consider updating to GDB {'.'.join(map(str, GDB_MIN_VERSION))} or higher "
            f"(with Python {'.'.join(map(str, PYTHON_MIN_VERSION))} or higher).")
        exit(1)

    try:
        pyenv = which("pyenv")
        PYENV_ROOT = gef_pystring(subprocess.check_output([pyenv, "root"]).strip())
        PYENV_VERSION = gef_pystring(subprocess.check_output([pyenv, "version-name"]).strip())
        site_packages_dir = os.path.join(PYENV_ROOT, "versions", PYENV_VERSION, "lib",
                                             f"python{PYENV_VERSION[:3]}", "site-packages")
        site.addsitedir(site_packages_dir)
    except FileNotFoundError:
        pass

    # When using a Python virtual environment, GDB still loads the system-installed Python
    # so GEF doesn't load site-packages dir from environment
    # In order to fix it, from the shell with venv activated we run the python binary,
    # take and parse its path, add the path to the current python process using sys.path.extend
    PYTHONBIN = which("python3")
    PREFIX = gef_pystring(subprocess.check_output([PYTHONBIN, '-c', 'import os, sys;print((sys.prefix))'])).strip("\\n")
    if PREFIX != sys.base_prefix:
        SITE_PACKAGES_DIRS = subprocess.check_output(
            [PYTHONBIN, "-c", "import os, sys;print(os.linesep.join(sys.path).strip())"]).decode("utf-8").split()
        sys.path.extend(SITE_PACKAGES_DIRS)

    # setup config
    gdb_initial_settings = (
        "set confirm off",
        "set verbose off",
        "set pagination off",
        "set print elements 0",
        "set history save on",
        "set history filename ~/.gdb_history",
        "set output-radix 0x10",
        "set print pretty on",
        "set architecture armv4t",
        "handle SIGALRM print nopass",
    )
    for cmd in gdb_initial_settings:
        try:
            gdb.execute(cmd)
        except gdb.error:
            pass

    # load GEF, set up the managers and load the plugins, functions,
    reset()
    gef.gdb.load()
    gef.gdb.show_banner()

    # load config
    gef.gdb.load_extra_plugins()

    # setup gdb prompt
    gdb.prompt_hook = __gef_prompt__

    # gdb events configuration
    gef_on_continue_hook(continue_handler)
    gef_on_stop_hook(hook_stop_handler)
    gef_on_new_hook(new_objfile_handler)
    gef_on_exit_hook(exit_handler)
    gef_on_memchanged_hook(memchanged_handler)
    gef_on_regchanged_hook(regchanged_handler)

    if gdb.current_progspace().filename is not None:
        # if here, we are sourcing gef from a gdb session already attached, force call to new_objfile (see issue #278)
        new_objfile_handler(None)

    GefTmuxSetup()
