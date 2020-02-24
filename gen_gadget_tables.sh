#!/bin/bash

(for kind in {ADD,SUB,MOV,XOR,XCHG}; do
    for dst in {EAX,ECX,EDX,EBX,ESP,EBP,ESI,EDI}; do
        echo -n "const ${kind}_${dst}_EXX: [&[u8]; 8] = [";
            (for reg in {eax,ecx,edx,ebx,esp,ebp,esi,edi}; do
                rasm2 "${kind} ${dst}, ${reg}" | sed 's/\(..\)/\\x\1/g; s/^.*$/\&*b"\0",/';
            done) | tr '\n' ' ';
        echo "];";
    done;
done) > src/arith_gadgets.generated.rs

(for cc in {A,AE,B,BE,C,E,G,GE,L,LE,NE,NO,NP,NS,O,P,S}; do
    echo -n "const CMOV${cc}_EAX_EXX: [&[u8]; 8] = [";
    (for reg in {eax,ecx,edx,ebx,esp,ebp,esi,edi}; do
        rasm2 "cmov$cc eax, $reg" | sed 's/\(..\)/\\x\1/g; s/^.*$/\&*b"\0",/';
    done) | tr '\n' ' ';
    echo "];";
done) > src/cmov_gadgets.generated.rs
