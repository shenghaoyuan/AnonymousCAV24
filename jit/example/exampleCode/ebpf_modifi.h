#include<stdio.h>
#include<stdint.h>
#include <inttypes.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

#define PRE 16
#define NUM 42
#define MAX_INS_NUM 500

_Bool is_lddw_low (uint64_t ins) {
  return (ins & 255LLU) == 0x18;
}

_Bool is_opcode_exit (uint64_t ins) {
  return (ins & 255LLU) == 0x95;
}

uint64_t fix_jump_opcode (uint64_t op) {
  switch (op) {
    case 0x16: return 0x15;
    case 0x26: return 0x25;
    case 0x36: return 0x35;
    case 0x46: return 0x45;
    case 0x56: return 0x55;
    case 0x66: return 0x65;
    case 0x76: return 0x75;
    case 0x86: return 0x85;
    
    case 0xa6: return 0xa5;
    case 0xb6: return 0xb5;
    case 0xc6: return 0xc5;
    case 0xd6: return 0xd5;
    
    case 0x1e: return 0x1d;
    case 0x2e: return 0x2d;
    case 0x3e: return 0x3d;
    case 0x4e: return 0x4d;
    case 0x5e: return 0x5d;
    case 0x6e: return 0x6d;
    case 0x7e: return 0x7d;
    case 0x8e: return 0x8d;
    
    case 0xae: return 0xad;
    case 0xbe: return 0xbd;
    case 0xce: return 0xcd;
    case 0xde: return 0xdd;
    default: return op;
  }
}
