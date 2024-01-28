from starkware.cairo.common.cairo_secp.bigint3 import BigInt3
from starkware.cairo.common.cairo_secp.ec_point import EcPoint
from starkware.cairo.common.cairo_secp.signature import recover_public_key

func call_recover_public_key{range_check_ptr}(
    msg_hash: BigInt3, r: BigInt3, s: BigInt3, v: felt
) -> (public_key_point: EcPoint) {
    return recover_public_key(msg_hash, r, s, v);
}
