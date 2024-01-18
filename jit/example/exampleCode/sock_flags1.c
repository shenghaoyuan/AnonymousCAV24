#include "bpf_sock.h"


uint32_t bpf_prog1(struct bpf_sock *sk, uint64_t gid_uid)
{
  uint32_t uid = gid_uid & 0xffffffff;
  uint32_t gid = gid_uid >> 32;
  if (sk->family == AF_INET6 &&
      sk->type == SOCK_DGRAM   &&
      sk->protocol == IPPROTO_ICMPV6)
    return uid;
  return gid;
}
