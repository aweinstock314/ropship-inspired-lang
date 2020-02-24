const ADD_EAX_EXX: [&[u8]; 8] = [&*b"\x01\xc0", &*b"\x01\xc8", &*b"\x01\xd0", &*b"\x01\xd8", &*b"\x01\xe0", &*b"\x01\xe8", &*b"\x01\xf0", &*b"\x01\xf8", ];
const ADD_ECX_EXX: [&[u8]; 8] = [&*b"\x01\xc1", &*b"\x01\xc9", &*b"\x01\xd1", &*b"\x01\xd9", &*b"\x01\xe1", &*b"\x01\xe9", &*b"\x01\xf1", &*b"\x01\xf9", ];
const ADD_EDX_EXX: [&[u8]; 8] = [&*b"\x01\xc2", &*b"\x01\xca", &*b"\x01\xd2", &*b"\x01\xda", &*b"\x01\xe2", &*b"\x01\xea", &*b"\x01\xf2", &*b"\x01\xfa", ];
const ADD_EBX_EXX: [&[u8]; 8] = [&*b"\x01\xc3", &*b"\x01\xcb", &*b"\x01\xd3", &*b"\x01\xdb", &*b"\x01\xe3", &*b"\x01\xeb", &*b"\x01\xf3", &*b"\x01\xfb", ];
const ADD_ESP_EXX: [&[u8]; 8] = [&*b"\x01\xc4", &*b"\x01\xcc", &*b"\x01\xd4", &*b"\x01\xdc", &*b"\x01\xe4", &*b"\x01\xec", &*b"\x01\xf4", &*b"\x01\xfc", ];
const ADD_EBP_EXX: [&[u8]; 8] = [&*b"\x01\xc5", &*b"\x01\xcd", &*b"\x01\xd5", &*b"\x01\xdd", &*b"\x01\xe5", &*b"\x01\xed", &*b"\x01\xf5", &*b"\x01\xfd", ];
const ADD_ESI_EXX: [&[u8]; 8] = [&*b"\x01\xc6", &*b"\x01\xce", &*b"\x01\xd6", &*b"\x01\xde", &*b"\x01\xe6", &*b"\x01\xee", &*b"\x01\xf6", &*b"\x01\xfe", ];
const ADD_EDI_EXX: [&[u8]; 8] = [&*b"\x01\xc7", &*b"\x01\xcf", &*b"\x01\xd7", &*b"\x01\xdf", &*b"\x01\xe7", &*b"\x01\xef", &*b"\x01\xf7", &*b"\x01\xff", ];
const SUB_EAX_EXX: [&[u8]; 8] = [&*b"\x29\xc0", &*b"\x29\xc8", &*b"\x29\xd0", &*b"\x29\xd8", &*b"\x29\xe0", &*b"\x29\xe8", &*b"\x29\xf0", &*b"\x29\xf8", ];
const SUB_ECX_EXX: [&[u8]; 8] = [&*b"\x29\xc1", &*b"\x29\xc9", &*b"\x29\xd1", &*b"\x29\xd9", &*b"\x29\xe1", &*b"\x29\xe9", &*b"\x29\xf1", &*b"\x29\xf9", ];
const SUB_EDX_EXX: [&[u8]; 8] = [&*b"\x29\xc2", &*b"\x29\xca", &*b"\x29\xd2", &*b"\x29\xda", &*b"\x29\xe2", &*b"\x29\xea", &*b"\x29\xf2", &*b"\x29\xfa", ];
const SUB_EBX_EXX: [&[u8]; 8] = [&*b"\x29\xc3", &*b"\x29\xcb", &*b"\x29\xd3", &*b"\x29\xdb", &*b"\x29\xe3", &*b"\x29\xeb", &*b"\x29\xf3", &*b"\x29\xfb", ];
const SUB_ESP_EXX: [&[u8]; 8] = [&*b"\x29\xc4", &*b"\x29\xcc", &*b"\x29\xd4", &*b"\x29\xdc", &*b"\x29\xe4", &*b"\x29\xec", &*b"\x29\xf4", &*b"\x29\xfc", ];
const SUB_EBP_EXX: [&[u8]; 8] = [&*b"\x29\xc5", &*b"\x29\xcd", &*b"\x29\xd5", &*b"\x29\xdd", &*b"\x29\xe5", &*b"\x29\xed", &*b"\x29\xf5", &*b"\x29\xfd", ];
const SUB_ESI_EXX: [&[u8]; 8] = [&*b"\x29\xc6", &*b"\x29\xce", &*b"\x29\xd6", &*b"\x29\xde", &*b"\x29\xe6", &*b"\x29\xee", &*b"\x29\xf6", &*b"\x29\xfe", ];
const SUB_EDI_EXX: [&[u8]; 8] = [&*b"\x29\xc7", &*b"\x29\xcf", &*b"\x29\xd7", &*b"\x29\xdf", &*b"\x29\xe7", &*b"\x29\xef", &*b"\x29\xf7", &*b"\x29\xff", ];
const MOV_EAX_EXX: [&[u8]; 8] = [&*b"\x89\xc0", &*b"\x89\xc8", &*b"\x89\xd0", &*b"\x89\xd8", &*b"\x89\xe0", &*b"\x89\xe8", &*b"\x89\xf0", &*b"\x89\xf8", ];
const MOV_ECX_EXX: [&[u8]; 8] = [&*b"\x89\xc1", &*b"\x89\xc9", &*b"\x89\xd1", &*b"\x89\xd9", &*b"\x89\xe1", &*b"\x89\xe9", &*b"\x89\xf1", &*b"\x89\xf9", ];
const MOV_EDX_EXX: [&[u8]; 8] = [&*b"\x89\xc2", &*b"\x89\xca", &*b"\x89\xd2", &*b"\x89\xda", &*b"\x89\xe2", &*b"\x89\xea", &*b"\x89\xf2", &*b"\x89\xfa", ];
const MOV_EBX_EXX: [&[u8]; 8] = [&*b"\x89\xc3", &*b"\x89\xcb", &*b"\x89\xd3", &*b"\x89\xdb", &*b"\x89\xe3", &*b"\x89\xeb", &*b"\x89\xf3", &*b"\x89\xfb", ];
const MOV_ESP_EXX: [&[u8]; 8] = [&*b"\x89\xc4", &*b"\x89\xcc", &*b"\x89\xd4", &*b"\x89\xdc", &*b"\x89\xe4", &*b"\x89\xec", &*b"\x89\xf4", &*b"\x89\xfc", ];
const MOV_EBP_EXX: [&[u8]; 8] = [&*b"\x89\xc5", &*b"\x89\xcd", &*b"\x89\xd5", &*b"\x89\xdd", &*b"\x89\xe5", &*b"\x89\xed", &*b"\x89\xf5", &*b"\x89\xfd", ];
const MOV_ESI_EXX: [&[u8]; 8] = [&*b"\x89\xc6", &*b"\x89\xce", &*b"\x89\xd6", &*b"\x89\xde", &*b"\x89\xe6", &*b"\x89\xee", &*b"\x89\xf6", &*b"\x89\xfe", ];
const MOV_EDI_EXX: [&[u8]; 8] = [&*b"\x89\xc7", &*b"\x89\xcf", &*b"\x89\xd7", &*b"\x89\xdf", &*b"\x89\xe7", &*b"\x89\xef", &*b"\x89\xf7", &*b"\x89\xff", ];
const XOR_EAX_EXX: [&[u8]; 8] = [&*b"\x31\xc0", &*b"\x31\xc8", &*b"\x31\xd0", &*b"\x31\xd8", &*b"\x31\xe0", &*b"\x31\xe8", &*b"\x31\xf0", &*b"\x31\xf8", ];
const XOR_ECX_EXX: [&[u8]; 8] = [&*b"\x31\xc1", &*b"\x31\xc9", &*b"\x31\xd1", &*b"\x31\xd9", &*b"\x31\xe1", &*b"\x31\xe9", &*b"\x31\xf1", &*b"\x31\xf9", ];
const XOR_EDX_EXX: [&[u8]; 8] = [&*b"\x31\xc2", &*b"\x31\xca", &*b"\x31\xd2", &*b"\x31\xda", &*b"\x31\xe2", &*b"\x31\xea", &*b"\x31\xf2", &*b"\x31\xfa", ];
const XOR_EBX_EXX: [&[u8]; 8] = [&*b"\x31\xc3", &*b"\x31\xcb", &*b"\x31\xd3", &*b"\x31\xdb", &*b"\x31\xe3", &*b"\x31\xeb", &*b"\x31\xf3", &*b"\x31\xfb", ];
const XOR_ESP_EXX: [&[u8]; 8] = [&*b"\x31\xc4", &*b"\x31\xcc", &*b"\x31\xd4", &*b"\x31\xdc", &*b"\x31\xe4", &*b"\x31\xec", &*b"\x31\xf4", &*b"\x31\xfc", ];
const XOR_EBP_EXX: [&[u8]; 8] = [&*b"\x31\xc5", &*b"\x31\xcd", &*b"\x31\xd5", &*b"\x31\xdd", &*b"\x31\xe5", &*b"\x31\xed", &*b"\x31\xf5", &*b"\x31\xfd", ];
const XOR_ESI_EXX: [&[u8]; 8] = [&*b"\x31\xc6", &*b"\x31\xce", &*b"\x31\xd6", &*b"\x31\xde", &*b"\x31\xe6", &*b"\x31\xee", &*b"\x31\xf6", &*b"\x31\xfe", ];
const XOR_EDI_EXX: [&[u8]; 8] = [&*b"\x31\xc7", &*b"\x31\xcf", &*b"\x31\xd7", &*b"\x31\xdf", &*b"\x31\xe7", &*b"\x31\xef", &*b"\x31\xf7", &*b"\x31\xff", ];
const XCHG_EAX_EXX: [&[u8]; 8] = [&*b"\x90", &*b"\x91", &*b"\x92", &*b"\x93", &*b"\x94", &*b"\x95", &*b"\x96", &*b"\x97", ];
const XCHG_ECX_EXX: [&[u8]; 8] = [&*b"\x91", &*b"\x87\xc9", &*b"\x87\xd1", &*b"\x87\xd9", &*b"\x87\xe1", &*b"\x87\xe9", &*b"\x87\xf1", &*b"\x87\xf9", ];
const XCHG_EDX_EXX: [&[u8]; 8] = [&*b"\x92", &*b"\x87\xca", &*b"\x87\xd2", &*b"\x87\xda", &*b"\x87\xe2", &*b"\x87\xea", &*b"\x87\xf2", &*b"\x87\xfa", ];
const XCHG_EBX_EXX: [&[u8]; 8] = [&*b"\x93", &*b"\x87\xcb", &*b"\x87\xd3", &*b"\x87\xdb", &*b"\x87\xe3", &*b"\x87\xeb", &*b"\x87\xf3", &*b"\x87\xfb", ];
const XCHG_ESP_EXX: [&[u8]; 8] = [&*b"\x94", &*b"\x87\xcc", &*b"\x87\xd4", &*b"\x87\xdc", &*b"\x87\xe4", &*b"\x87\xec", &*b"\x87\xf4", &*b"\x87\xfc", ];
const XCHG_EBP_EXX: [&[u8]; 8] = [&*b"\x95", &*b"\x87\xcd", &*b"\x87\xd5", &*b"\x87\xdd", &*b"\x87\xe5", &*b"\x87\xed", &*b"\x87\xf5", &*b"\x87\xfd", ];
const XCHG_ESI_EXX: [&[u8]; 8] = [&*b"\x96", &*b"\x87\xce", &*b"\x87\xd6", &*b"\x87\xde", &*b"\x87\xe6", &*b"\x87\xee", &*b"\x87\xf6", &*b"\x87\xfe", ];
const XCHG_EDI_EXX: [&[u8]; 8] = [&*b"\x97", &*b"\x87\xcf", &*b"\x87\xd7", &*b"\x87\xdf", &*b"\x87\xe7", &*b"\x87\xef", &*b"\x87\xf7", &*b"\x87\xff", ];