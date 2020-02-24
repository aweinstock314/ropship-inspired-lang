const XCHG_EAX_EXX: [&[u8]; 8] = [&*b"\x90", &*b"\x91", &*b"\x92", &*b"\x93", &*b"\x94", &*b"\x95", &*b"\x96", &*b"\x97", ];
const XCHG_ESI_EXX: [&[u8]; 8] = [&*b"\x96", &*b"\x87\xce", &*b"\x87\xd6", &*b"\x87\xde", &*b"\x87\xe6", &*b"\x87\xee", &*b"\x87\xf6", &*b"\x87\xfe", ];
const XCHG_EDI_EXX: [&[u8]; 8] = [&*b"\x97", &*b"\x87\xcf", &*b"\x87\xd7", &*b"\x87\xdf", &*b"\x87\xe7", &*b"\x87\xef", &*b"\x87\xf7", &*b"\x87\xff", ];
