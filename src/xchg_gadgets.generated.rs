const XCHG_EAX_EXX: [&[u8]; 8] = [&*b"\x90", &*b"\x91", &*b"\x92", &*b"\x93", &*b"\x94", &*b"\x95", &*b"\x96", &*b"\x97", ];
const XCHG_ECX_EXX: [&[u8]; 8] = [&*b"\x91", &*b"\x87\xc9", &*b"\x87\xd1", &*b"\x87\xd9", &*b"\x87\xe1", &*b"\x87\xe9", &*b"\x87\xf1", &*b"\x87\xf9", ];
const XCHG_EDX_EXX: [&[u8]; 8] = [&*b"\x92", &*b"\x87\xca", &*b"\x87\xd2", &*b"\x87\xda", &*b"\x87\xe2", &*b"\x87\xea", &*b"\x87\xf2", &*b"\x87\xfa", ];
const XCHG_EBX_EXX: [&[u8]; 8] = [&*b"\x93", &*b"\x87\xcb", &*b"\x87\xd3", &*b"\x87\xdb", &*b"\x87\xe3", &*b"\x87\xeb", &*b"\x87\xf3", &*b"\x87\xfb", ];
const XCHG_ESP_EXX: [&[u8]; 8] = [&*b"\x94", &*b"\x87\xcc", &*b"\x87\xd4", &*b"\x87\xdc", &*b"\x87\xe4", &*b"\x87\xec", &*b"\x87\xf4", &*b"\x87\xfc", ];
const XCHG_EBP_EXX: [&[u8]; 8] = [&*b"\x95", &*b"\x87\xcd", &*b"\x87\xd5", &*b"\x87\xdd", &*b"\x87\xe5", &*b"\x87\xed", &*b"\x87\xf5", &*b"\x87\xfd", ];
const XCHG_ESI_EXX: [&[u8]; 8] = [&*b"\x96", &*b"\x87\xce", &*b"\x87\xd6", &*b"\x87\xde", &*b"\x87\xe6", &*b"\x87\xee", &*b"\x87\xf6", &*b"\x87\xfe", ];
const XCHG_EDI_EXX: [&[u8]; 8] = [&*b"\x97", &*b"\x87\xcf", &*b"\x87\xd7", &*b"\x87\xdf", &*b"\x87\xe7", &*b"\x87\xef", &*b"\x87\xf7", &*b"\x87\xff", ];
