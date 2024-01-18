#include "bpf_sock.h"


uint32_t bpf_prog1(struct bpf_sock *sk)
{
  if (sk->family == AF_INET &&
      sk->type == SOCK_DGRAM   &&
      sk->protocol == IPPROTO_ICMP)
    return 0;
  return 1;
}
