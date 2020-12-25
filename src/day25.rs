fn transform(loop_size: usize, subject_number: usize) -> usize {
    let mut value = 1;
    for _ in 0..loop_size {
        value = (value * subject_number) % 20201227;
    }
    value
}

fn determine_loop_size(public_key: usize) -> usize {
    let mut value = 1;
    for i in 1.. {
        value = (value * 7) % 20201227;
        if value == public_key {
            return i
        }
    }
    0
}

pub fn main() {
    /*
    let card_pubkey = 5764801;
    let door_pubkey = 17807724;
    assert_eq!(Encrypter::transform(8, 7), card_pubkey);
    assert_eq!(Encrypter::transform(11, 7), door_pubkey);

    let card_loop_size = Encrypter::determine_loop_size(card_pubkey);
    let door_loop_size = Encrypter::determine_loop_size(door_pubkey);

    let encryption_key_by_card = Encrypter::transform(card_loop_size, door_pubkey);
    let encryption_key_by_door = Encrypter::transform(door_loop_size, card_pubkey);
    dbg!(encryption_key_by_card);
    dbg!(encryption_key_by_door);

    assert_eq!(encryption_key_by_card, encryption_key_by_door);
     */

    let card_pubkey = 12320657;
    let door_pubkey = 9659666;
    let card_loop_size = determine_loop_size(card_pubkey);
    let door_loop_size = determine_loop_size(door_pubkey);
    assert_eq!(transform(card_loop_size, 7), card_pubkey);
    assert_eq!(transform(door_loop_size, 7), door_pubkey);

    dbg!((card_loop_size, door_loop_size));
    let encryption_key_by_card = transform(card_loop_size, door_pubkey);
    let encryption_key_by_door = transform(door_loop_size, card_pubkey);
    dbg!(encryption_key_by_card);
    dbg!(encryption_key_by_door);

    assert_eq!(encryption_key_by_card, encryption_key_by_door);
}
