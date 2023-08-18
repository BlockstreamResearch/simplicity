/* This file has been automatically generated. */
[ADD_16] =
{ .tag = JET
, .jet = add_16
, .cmr = {{0xab710d45u, 0xbdda1ee2u, 0x4eb18f64u, 0xb955acc2u, 0x7f07639eu, 0x22a02905u, 0x3812b6f5u, 0xacd00c05u}}
, .sourceIx = ty_w32
, .targetIx = ty_pbw16
, .cost = 133 /* milli weight units */
}
,[ADD_32] =
{ .tag = JET
, .jet = add_32
, .cmr = {{0x91ed4c3du, 0x0d94d111u, 0xc72bd431u, 0xc0acbb0du, 0xe1c58995u, 0x640b58cfu, 0x70d37eadu, 0xb740101au}}
, .sourceIx = ty_w64
, .targetIx = ty_pbw32
, .cost = 133 /* milli weight units */
}
,[ADD_64] =
{ .tag = JET
, .jet = add_64
, .cmr = {{0xa5e6556au, 0x21cce105u, 0xe994e165u, 0xa403657eu, 0xea7eef36u, 0x1b104104u, 0x5ff326a3u, 0x2702aafeu}}
, .sourceIx = ty_w128
, .targetIx = ty_pbw64
, .cost = 133 /* milli weight units */
}
,[ADD_8] =
{ .tag = JET
, .jet = add_8
, .cmr = {{0x51e5af2cu, 0x99e0d4d3u, 0x93430b3eu, 0xd32db083u, 0xa9a02064u, 0x6d36644eu, 0x5470bb9du, 0xb9fd0e22u}}
, .sourceIx = ty_w16
, .targetIx = ty_pbw8
, .cost = 133 /* milli weight units */
}
,[ALL_16] =
{ .tag = JET
, .jet = all_16
, .cmr = {{0xccc00686u, 0x73e30d34u, 0x42e61648u, 0x7a4b53a1u, 0x95f5c2cfu, 0x13891cc6u, 0x3f7e862bu, 0xa0d929a8u}}
, .sourceIx = ty_w16
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[ALL_32] =
{ .tag = JET
, .jet = all_32
, .cmr = {{0xb2c0d77fu, 0xebc6f173u, 0xb142c2b6u, 0x2bb8f5fdu, 0xbd379a1du, 0x7ddf8951u, 0x3360a02eu, 0xeb419400u}}
, .sourceIx = ty_w32
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[ALL_64] =
{ .tag = JET
, .jet = all_64
, .cmr = {{0x1c9a3a89u, 0x5a18e1e7u, 0x8182130du, 0xdfc8972au, 0x28ae45e4u, 0xb4eafd1bu, 0xcfed5dd6u, 0x090657ffu}}
, .sourceIx = ty_w64
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[ALL_8] =
{ .tag = JET
, .jet = all_8
, .cmr = {{0xd7f50ec5u, 0x6503b329u, 0x96959de1u, 0xad4867b8u, 0xb059d96au, 0xc8cc4e1du, 0x4f89607fu, 0x060ed146u}}
, .sourceIx = ty_w8
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[AND_16] =
{ .tag = JET
, .jet = and_16
, .cmr = {{0x922f864bu, 0xa8dc2b6bu, 0x9d31634du, 0x3116cb38u, 0xd1ae0d7cu, 0x2150ea1du, 0x4aec1fa3u, 0x93acf6f2u}}
, .sourceIx = ty_w32
, .targetIx = ty_w16
, .cost = 133 /* milli weight units */
}
,[AND_32] =
{ .tag = JET
, .jet = and_32
, .cmr = {{0xe8ad05b4u, 0x6cf62c0du, 0x484542a6u, 0xbb43f9aau, 0xdf0e148bu, 0xd345e662u, 0x5117ab61u, 0xedea0bd5u}}
, .sourceIx = ty_w64
, .targetIx = ty_w32
, .cost = 133 /* milli weight units */
}
,[AND_64] =
{ .tag = JET
, .jet = and_64
, .cmr = {{0x7971f18cu, 0x00cff166u, 0xa0d21b7au, 0x18f0edc8u, 0x0ec7d392u, 0x71e413efu, 0x0825e497u, 0xb0ca2d1cu}}
, .sourceIx = ty_w128
, .targetIx = ty_w64
, .cost = 133 /* milli weight units */
}
,[AND_8] =
{ .tag = JET
, .jet = and_8
, .cmr = {{0x58336536u, 0x0becef53u, 0xc3190dcdu, 0xa5451675u, 0xd720df45u, 0xb0674340u, 0x8bcd6643u, 0xae3580dbu}}
, .sourceIx = ty_w16
, .targetIx = ty_w8
, .cost = 133 /* milli weight units */
}
,[ANNEX_HASH] =
{ .tag = JET
, .jet = annex_hash
, .cmr = {{0xb69c9e4cu, 0xd51f22c2u, 0xa19133efu, 0x3295b8e4u, 0xe5d7dd39u, 0x911008aau, 0x6a5e6d8fu, 0x1722ea1du}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256mw256
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 465 /* milli weight units */
}
,[ASSET_AMOUNT_HASH] =
{ .tag = JET
, .jet = asset_amount_hash
, .cmr = {{0xf71799b8u, 0x373778e1u, 0xd91e161au, 0xd4f43509u, 0x067605c2u, 0xe77a3161u, 0xfcc358eeu, 0xfcef4157u}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256pspbw256w256spbw256w64
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 399 /* milli weight units */
}
,[BIP_0340_VERIFY] =
{ .tag = JET
, .jet = bip_0340_verify
, .cmr = {{0xea0f81fau, 0x0ac2e203u, 0x62cb0961u, 0x2d199fccu, 0x45be91b0u, 0xd58d8782u, 0x2572e9ecu, 0xe24e10c1u}}
, .sourceIx = ty_w1Ki
, .targetIx = ty_u
, .cost = 50735 /* milli weight units */
}
,[BUILD_TAPBRANCH] =
{ .tag = JET
, .jet = build_tapbranch
, .cmr = {{0x337ff42du, 0xe041b602u, 0xd75764ceu, 0xa48219ecu, 0x2aaf7e8eu, 0x5bc03508u, 0x6a006901u, 0xf2795403u}}
, .sourceIx = ty_w512
, .targetIx = ty_w256
, .cost = 3167 /* milli weight units */
}
,[BUILD_TAPLEAF_SIMPLICITY] =
{ .tag = JET
, .jet = build_tapleaf_simplicity
, .cmr = {{0x3a62c764u, 0xf6da8adeu, 0x19086bfbu, 0x7575c231u, 0x474007f0u, 0x6ab4f40au, 0x58938544u, 0x924834d2u}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 2240 /* milli weight units */
}
,[CALCULATE_ASSET] =
{ .tag = JET
, .jet = calculate_asset
, .cmr = {{0x591ab7a5u, 0x1e1469d1u, 0x3b5546e5u, 0xcf3d2455u, 0xaea9513au, 0x822cdb12u, 0xd2cd1c9du, 0x330f0f7bu}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 794 /* milli weight units */
}
,[CALCULATE_CONFIDENTIAL_TOKEN] =
{ .tag = JET
, .jet = calculate_confidential_token
, .cmr = {{0xda2a8868u, 0xfda8fcd1u, 0xb5304920u, 0xbdecd669u, 0x085f8539u, 0x7d39bf1fu, 0xff8aa57du, 0xf8a31ab4u}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 774 /* milli weight units */
}
,[CALCULATE_EXPLICIT_TOKEN] =
{ .tag = JET
, .jet = calculate_explicit_token
, .cmr = {{0x9b419828u, 0xaea6ac84u, 0x802be128u, 0x83491fe4u, 0x9b076c25u, 0x812bded8u, 0xba3874bfu, 0x9560aae6u}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 769 /* milli weight units */
}
,[CALCULATE_ISSUANCE_ENTROPY] =
{ .tag = JET
, .jet = calculate_issuance_entropy
, .cmr = {{0x1df7ec05u, 0xe1a98dd3u, 0x7b6d8c48u, 0x0a21bcd0u, 0x4319e750u, 0x5393b6f6u, 0x457b50c7u, 0x78f705a3u}}
, .sourceIx = ty_ppw256w32w256
, .targetIx = ty_w256
, .cost = 3564 /* milli weight units */
}
,[CH_16] =
{ .tag = JET
, .jet = ch_16
, .cmr = {{0xc6dd7170u, 0xc5f67268u, 0x317e195eu, 0x8b30eaf3u, 0x4c23b00cu, 0x5ab9c31eu, 0xed33e52du, 0xbf00f512u}}
, .sourceIx = ty_pw16w32
, .targetIx = ty_w16
, .cost = 133 /* milli weight units */
}
,[CH_32] =
{ .tag = JET
, .jet = ch_32
, .cmr = {{0x51bb4845u, 0x664f601du, 0xa40daf5eu, 0x2a6f0e1bu, 0x4fed705cu, 0xb0006059u, 0x358a06d6u, 0x743ebab9u}}
, .sourceIx = ty_pw32w64
, .targetIx = ty_w32
, .cost = 133 /* milli weight units */
}
,[CH_64] =
{ .tag = JET
, .jet = ch_64
, .cmr = {{0x16870997u, 0xe0fb1fbeu, 0xfe81cc21u, 0x6d724d6fu, 0x44b3163bu, 0x333178ffu, 0x3606c567u, 0x24829657u}}
, .sourceIx = ty_pw64w128
, .targetIx = ty_w64
, .cost = 133 /* milli weight units */
}
,[CH_8] =
{ .tag = JET
, .jet = ch_8
, .cmr = {{0x1f6e225bu, 0x369a7589u, 0x0bd5d7a6u, 0xca40f483u, 0x47f1b194u, 0xf5147a1bu, 0x1b10f860u, 0xf93522a8u}}
, .sourceIx = ty_pw8w16
, .targetIx = ty_w8
, .cost = 133 /* milli weight units */
}
,[CHECK_LOCK_DISTANCE] =
{ .tag = JET
, .jet = check_lock_distance
, .cmr = {{0xbe2daf31u, 0xa927eab2u, 0x5cd29615u, 0x31d57f5au, 0x75d60782u, 0xaa965628u, 0x23746687u, 0x2ac9be58u}}
, .sourceIx = ty_w16
, .targetIx = ty_u
, .cost = 168 /* milli weight units */
}
,[CHECK_LOCK_DURATION] =
{ .tag = JET
, .jet = check_lock_duration
, .cmr = {{0x3afa7301u, 0xeb46a130u, 0x53411a2au, 0xc4be6808u, 0x5a45b3fbu, 0x8d64a075u, 0x1af86980u, 0x1be57ff2u}}
, .sourceIx = ty_w16
, .targetIx = ty_u
, .cost = 182 /* milli weight units */
}
,[CHECK_LOCK_HEIGHT] =
{ .tag = JET
, .jet = check_lock_height
, .cmr = {{0x0769e002u, 0xa0c678f8u, 0xb3106381u, 0x0c0b20bcu, 0xe2a24d63u, 0xdd03c8f1u, 0xa5a59917u, 0xbc7356eeu}}
, .sourceIx = ty_w32
, .targetIx = ty_u
, .cost = 117 /* milli weight units */
}
,[CHECK_LOCK_TIME] =
{ .tag = JET
, .jet = check_lock_time
, .cmr = {{0xbc203552u, 0x709243f2u, 0x6d0fbadcu, 0xba279bf0u, 0x2e4c4295u, 0xb55e4768u, 0x4970cbffu, 0xbbd2599eu}}
, .sourceIx = ty_w32
, .targetIx = ty_u
, .cost = 95 /* milli weight units */
}
,[CHECK_SIG_VERIFY] =
{ .tag = JET
, .jet = check_sig_verify
, .cmr = {{0xe8feb534u, 0x34e2bdb5u, 0xcfe6a91fu, 0xa8f9e177u, 0xf941a67cu, 0xc6ced869u, 0x746f1a8eu, 0xb6506f76u}}
, .sourceIx = ty_ppw256w512w512
, .targetIx = ty_u
, .cost = 50000 /* milli weight units */
}
,[COMPLEMENT_16] =
{ .tag = JET
, .jet = complement_16
, .cmr = {{0x353d1a7fu, 0x4d547955u, 0x4229c743u, 0xeda65b6au, 0xe2019a36u, 0x51969bd6u, 0x52a142c3u, 0x1904dcbau}}
, .sourceIx = ty_w16
, .targetIx = ty_w16
, .cost = 133 /* milli weight units */
}
,[COMPLEMENT_32] =
{ .tag = JET
, .jet = complement_32
, .cmr = {{0x29e539b4u, 0xf8604e79u, 0xe75c1790u, 0x88eb7308u, 0xeb108cc6u, 0xe334c509u, 0x81c88b70u, 0x4f1c7c5bu}}
, .sourceIx = ty_w32
, .targetIx = ty_w32
, .cost = 133 /* milli weight units */
}
,[COMPLEMENT_64] =
{ .tag = JET
, .jet = complement_64
, .cmr = {{0x1628873au, 0x31d5aacfu, 0x5578ba26u, 0xc58bb795u, 0x3bf62b87u, 0x1a159877u, 0xb148840cu, 0x22e8598du}}
, .sourceIx = ty_w64
, .targetIx = ty_w64
, .cost = 133 /* milli weight units */
}
,[COMPLEMENT_8] =
{ .tag = JET
, .jet = complement_8
, .cmr = {{0x13d1c524u, 0xc9f6e88fu, 0xda60a89fu, 0x41b82da7u, 0xbd988d98u, 0xf90f6bfau, 0x6974167du, 0xe7314c30u}}
, .sourceIx = ty_w8
, .targetIx = ty_w8
, .cost = 133 /* milli weight units */
}
,[CURRENT_AMOUNT] =
{ .tag = JET
, .jet = current_amount
, .cmr = {{0x59af46d9u, 0xd0deab49u, 0xc4ff2bdbu, 0xfcc56ab8u, 0xb3ceeed4u, 0x223f7c94u, 0x803ff1b3u, 0xd1f57220u}}
, .sourceIx = ty_u
, .targetIx = ty_pspbw256w256spbw256w64
, .cost = 299 /* milli weight units */
}
,[CURRENT_ANNEX_HASH] =
{ .tag = JET
, .jet = current_annex_hash
, .cmr = {{0xba5e7041u, 0xff93cb3cu, 0x00a56840u, 0x7ce96575u, 0x7b6b520cu, 0x452484d7u, 0x7778497bu, 0x57b01c1au}}
, .sourceIx = ty_u
, .targetIx = ty_mw256
, .cost = 128 /* milli weight units */
}
,[CURRENT_ASSET] =
{ .tag = JET
, .jet = current_asset
, .cmr = {{0xf0c3eddcu, 0x28e224c3u, 0xc0a07889u, 0x0d28169eu, 0xa9e18791u, 0xc1a6f7a8u, 0xade8e811u, 0xc50b7d89u}}
, .sourceIx = ty_u
, .targetIx = ty_spbw256w256
, .cost = 158 /* milli weight units */
}
,[CURRENT_INDEX] =
{ .tag = JET
, .jet = current_index
, .cmr = {{0x31ffebcbu, 0x633e5be9u, 0x2c3d4d7cu, 0x28589d39u, 0x0da513f9u, 0x8df28bc4u, 0xacc31b2eu, 0x6dfad50eu}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 59 /* milli weight units */
}
,[CURRENT_ISSUANCE_ASSET_AMOUNT] =
{ .tag = JET
, .jet = current_issuance_asset_amount
, .cmr = {{0xad567be3u, 0x638365e5u, 0xcf93d8d8u, 0x9657150fu, 0xd85cfe58u, 0x7869911bu, 0x0dbf264fu, 0xb2f944a4u}}
, .sourceIx = ty_u
, .targetIx = ty_mspbw256w64
, .cost = 132 /* milli weight units */
}
,[CURRENT_ISSUANCE_ASSET_PROOF] =
{ .tag = JET
, .jet = current_issuance_asset_proof
, .cmr = {{0xad2cdb8fu, 0x66f9e215u, 0x8ee7b6d3u, 0x7615a018u, 0x1faf9b5bu, 0x96b6c4e7u, 0x031c776du, 0xf9b5408fu}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 129 /* milli weight units */
}
,[CURRENT_ISSUANCE_TOKEN_AMOUNT] =
{ .tag = JET
, .jet = current_issuance_token_amount
, .cmr = {{0x03f211cfu, 0x6f2a0ffbu, 0xf0483573u, 0xeec604b4u, 0x2e9d7bfbu, 0x5529bcdfu, 0x4a9b0b72u, 0x0dba31beu}}
, .sourceIx = ty_u
, .targetIx = ty_mspbw256w64
, .cost = 127 /* milli weight units */
}
,[CURRENT_ISSUANCE_TOKEN_PROOF] =
{ .tag = JET
, .jet = current_issuance_token_proof
, .cmr = {{0x5b278a3fu, 0x6a6ebed0u, 0xd57ac92cu, 0xb83fca37u, 0x12b616b9u, 0x99f908a9u, 0x83ecce43u, 0x85dd6aadu}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 143 /* milli weight units */
}
,[CURRENT_NEW_ISSUANCE_CONTRACT] =
{ .tag = JET
, .jet = current_new_issuance_contract
, .cmr = {{0xbefb45e9u, 0x4925b636u, 0x217cc394u, 0x630e9792u, 0x8f0ce6f9u, 0x64549a61u, 0x3c196f53u, 0x3c778fa5u}}
, .sourceIx = ty_u
, .targetIx = ty_mw256
, .cost = 146 /* milli weight units */
}
,[CURRENT_PEGIN] =
{ .tag = JET
, .jet = current_pegin
, .cmr = {{0xfcbccf45u, 0x0b64d429u, 0x052937d0u, 0x665dd2e4u, 0xd354b8aeu, 0xf4fb0aceu, 0xfde827b4u, 0x32d2702bu}}
, .sourceIx = ty_u
, .targetIx = ty_mw256
, .cost = 120 /* milli weight units */
}
,[CURRENT_PREV_OUTPOINT] =
{ .tag = JET
, .jet = current_prev_outpoint
, .cmr = {{0xccaa9649u, 0xd582ff08u, 0x649ef515u, 0x2911ae10u, 0x73e711c0u, 0x22402bf2u, 0xdeab570au, 0xb50e4bdcu}}
, .sourceIx = ty_u
, .targetIx = ty_pw256w32
, .cost = 120 /* milli weight units */
}
,[CURRENT_REISSUANCE_BLINDING] =
{ .tag = JET
, .jet = current_reissuance_blinding
, .cmr = {{0x7489a09cu, 0x2b0646b4u, 0xbf392c6fu, 0x1646654cu, 0x5fea6b67u, 0xc6352b60u, 0xc0864f45u, 0x8f5136bau}}
, .sourceIx = ty_u
, .targetIx = ty_mw256
, .cost = 200 /* milli weight units */
}
,[CURRENT_REISSUANCE_ENTROPY] =
{ .tag = JET
, .jet = current_reissuance_entropy
, .cmr = {{0xa47b8246u, 0x89511e5eu, 0x655438f6u, 0xab2c0752u, 0x14128cd7u, 0x7f05935cu, 0x13cad401u, 0xb7d29652u}}
, .sourceIx = ty_u
, .targetIx = ty_mw256
, .cost = 73 /* milli weight units */
}
,[CURRENT_SCRIPT_HASH] =
{ .tag = JET
, .jet = current_script_hash
, .cmr = {{0x0e152132u, 0x6ae08a41u, 0xaac66506u, 0xd23e7978u, 0xeea3cd99u, 0x93c0f1dfu, 0xf24dad7cu, 0x01347010u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 188 /* milli weight units */
}
,[CURRENT_SCRIPT_SIG_HASH] =
{ .tag = JET
, .jet = current_script_sig_hash
, .cmr = {{0x44fbc75cu, 0xe30a75a2u, 0xd543060fu, 0x73f6ec62u, 0xe9752f44u, 0x311738b1u, 0xa9b2b877u, 0xd2cd786cu}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 542 /* milli weight units */
}
,[CURRENT_SEQUENCE] =
{ .tag = JET
, .jet = current_sequence
, .cmr = {{0x5e5b4da3u, 0x3ec256dcu, 0xa6857896u, 0xccaf671du, 0x58c0a80au, 0xf0d1bf85u, 0x52489d45u, 0x46d815c7u}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 147 /* milli weight units */
}
,[DECOMPRESS] =
{ .tag = JET
, .jet = decompress
, .cmr = {{0x419c87e5u, 0xe9034b5du, 0x453fa668u, 0x19db5a36u, 0xa4a58435u, 0x68833e85u, 0x70ec7729u, 0xb10a40a5u}}
, .sourceIx = ty_pbw256
, .targetIx = ty_mw512
, .cost = 11173 /* milli weight units */
}
,[DECREMENT_16] =
{ .tag = JET
, .jet = decrement_16
, .cmr = {{0xb483b1e9u, 0xd9ef7410u, 0x6833f66fu, 0x680c226eu, 0xf698223cu, 0x26cf8de5u, 0x72ed540fu, 0x2c126dafu}}
, .sourceIx = ty_w16
, .targetIx = ty_pbw16
, .cost = 109 /* milli weight units */
}
,[DECREMENT_32] =
{ .tag = JET
, .jet = decrement_32
, .cmr = {{0x8266c07du, 0x1cbf8f65u, 0xa3eb8fd3u, 0x2ef60601u, 0xce289ffbu, 0x03ae3e37u, 0x5b9c7610u, 0x357fe9dfu}}
, .sourceIx = ty_w32
, .targetIx = ty_pbw32
, .cost = 109 /* milli weight units */
}
,[DECREMENT_64] =
{ .tag = JET
, .jet = decrement_64
, .cmr = {{0x6ee6d1a4u, 0x965d3785u, 0xbff0a3e1u, 0xe1690b16u, 0xfdce2b32u, 0x61c77719u, 0xafb69c8fu, 0xab4b9a5au}}
, .sourceIx = ty_w64
, .targetIx = ty_pbw64
, .cost = 109 /* milli weight units */
}
,[DECREMENT_8] =
{ .tag = JET
, .jet = decrement_8
, .cmr = {{0xa75fe622u, 0x50993fb4u, 0xd537ae86u, 0xf3014519u, 0x2466df31u, 0x27d5ac2du, 0x420a7b71u, 0x7498b548u}}
, .sourceIx = ty_w8
, .targetIx = ty_pbw8
, .cost = 109 /* milli weight units */
}
,[DIV_MOD_16] =
{ .tag = JET
, .jet = div_mod_16
, .cmr = {{0x071a9fc0u, 0xa534e752u, 0x492874a9u, 0xdc1ec531u, 0xd07d0c22u, 0x0995ced1u, 0x227a1ac1u, 0xe3e7f1a7u}}
, .sourceIx = ty_w32
, .targetIx = ty_w32
, .cost = 138 /* milli weight units */
}
,[DIV_MOD_32] =
{ .tag = JET
, .jet = div_mod_32
, .cmr = {{0x937f39aau, 0x8e26a766u, 0x52ed51cdu, 0xb7d489b9u, 0x33273f27u, 0x5bde68f5u, 0x4e59b49bu, 0x266b6f8cu}}
, .sourceIx = ty_w64
, .targetIx = ty_w64
, .cost = 138 /* milli weight units */
}
,[DIV_MOD_64] =
{ .tag = JET
, .jet = div_mod_64
, .cmr = {{0xa2681727u, 0x26402856u, 0x537139cdu, 0x0a23fe34u, 0x03b765efu, 0x74b577dcu, 0x61fdb20du, 0x4d7ac4dfu}}
, .sourceIx = ty_w128
, .targetIx = ty_w128
, .cost = 138 /* milli weight units */
}
,[DIV_MOD_8] =
{ .tag = JET
, .jet = div_mod_8
, .cmr = {{0xbf7caf50u, 0xceae7b12u, 0xb38d82c9u, 0x3e460193u, 0x6941f605u, 0x73df98e7u, 0x2a9c5a13u, 0x490739d2u}}
, .sourceIx = ty_w16
, .targetIx = ty_w16
, .cost = 138 /* milli weight units */
}
,[DIVIDE_16] =
{ .tag = JET
, .jet = divide_16
, .cmr = {{0x50797313u, 0xf76dd655u, 0x85ef828cu, 0xe01cdc13u, 0x2a489cdau, 0xff434986u, 0xdd8999dbu, 0xdeaa617bu}}
, .sourceIx = ty_w32
, .targetIx = ty_w16
, .cost = 138 /* milli weight units */
}
,[DIVIDE_32] =
{ .tag = JET
, .jet = divide_32
, .cmr = {{0x4df2a125u, 0x5f071f8au, 0x2bfc9a80u, 0x5edf99d3u, 0xc890f5b1u, 0xc4b81a8fu, 0xa6a96c95u, 0xcea1a3fbu}}
, .sourceIx = ty_w64
, .targetIx = ty_w32
, .cost = 138 /* milli weight units */
}
,[DIVIDE_64] =
{ .tag = JET
, .jet = divide_64
, .cmr = {{0xba62d187u, 0xb9602430u, 0xd0001d91u, 0xd1223fedu, 0x7928d320u, 0x95aefc57u, 0x22e4b30cu, 0xe6ac1cf4u}}
, .sourceIx = ty_w128
, .targetIx = ty_w64
, .cost = 138 /* milli weight units */
}
,[DIVIDE_8] =
{ .tag = JET
, .jet = divide_8
, .cmr = {{0xcd0eb6f3u, 0x2f77e2d9u, 0x7808064eu, 0x961dab46u, 0xee3e2647u, 0xb2357a7bu, 0x5892d36fu, 0xbc232dc0u}}
, .sourceIx = ty_w16
, .targetIx = ty_w8
, .cost = 138 /* milli weight units */
}
,[DIVIDES_16] =
{ .tag = JET
, .jet = divides_16
, .cmr = {{0x0ad60f11u, 0xf0123e30u, 0x4a9b7772u, 0x5ca65e70u, 0xb7106b4du, 0x05644ac6u, 0xd8452a56u, 0xe7fb6f90u}}
, .sourceIx = ty_w32
, .targetIx = ty_b
, .cost = 138 /* milli weight units */
}
,[DIVIDES_32] =
{ .tag = JET
, .jet = divides_32
, .cmr = {{0xd65a4793u, 0x65d8ef47u, 0xe457016cu, 0xf3e4c127u, 0x89103668u, 0x5492cb85u, 0xf8cc2cc1u, 0x77171113u}}
, .sourceIx = ty_w64
, .targetIx = ty_b
, .cost = 138 /* milli weight units */
}
,[DIVIDES_64] =
{ .tag = JET
, .jet = divides_64
, .cmr = {{0xb73ddbb9u, 0x32c8b860u, 0xe82e992au, 0xcc7259a7u, 0x8c0fdd32u, 0x009036efu, 0x65c47608u, 0x368b03c8u}}
, .sourceIx = ty_w128
, .targetIx = ty_b
, .cost = 138 /* milli weight units */
}
,[DIVIDES_8] =
{ .tag = JET
, .jet = divides_8
, .cmr = {{0xe4240f08u, 0x24df3aceu, 0x65093626u, 0x003a6b97u, 0x5d27fe89u, 0xaf199921u, 0x4d438b05u, 0xf1a159edu}}
, .sourceIx = ty_w16
, .targetIx = ty_b
, .cost = 138 /* milli weight units */
}
,[EQ_16] =
{ .tag = JET
, .jet = eq_16
, .cmr = {{0x05dfefd7u, 0x4a26ab79u, 0x89a85093u, 0x31a03f33u, 0x401821a0u, 0x1a7504e8u, 0x09b11412u, 0x8226d6fdu}}
, .sourceIx = ty_w32
, .targetIx = ty_b
, .cost = 69 /* milli weight units */
}
,[EQ_256] =
{ .tag = JET
, .jet = eq_256
, .cmr = {{0xf52749f1u, 0xf2fcdaafu, 0xa36254f1u, 0x63e67046u, 0xe4881eedu, 0xcafd1701u, 0x5e98e0ccu, 0x1441a544u}}
, .sourceIx = ty_w512
, .targetIx = ty_b
, .cost = 153 /* milli weight units */
}
,[EQ_32] =
{ .tag = JET
, .jet = eq_32
, .cmr = {{0xd49ec01cu, 0x58a1d955u, 0xcaeb56f7u, 0xd7b0f39fu, 0x1819a9d2u, 0xbdcd34cbu, 0x108b63e3u, 0x122e04c6u}}
, .sourceIx = ty_w64
, .targetIx = ty_b
, .cost = 69 /* milli weight units */
}
,[EQ_64] =
{ .tag = JET
, .jet = eq_64
, .cmr = {{0xf19689adu, 0x947e2455u, 0x89a4e187u, 0x1a1752c6u, 0x66666b43u, 0x427909fbu, 0x3acd95f0u, 0x8bc6930au}}
, .sourceIx = ty_w128
, .targetIx = ty_b
, .cost = 69 /* milli weight units */
}
,[EQ_8] =
{ .tag = JET
, .jet = eq_8
, .cmr = {{0x7b7eb829u, 0x738d383cu, 0xc25fbd59u, 0xc7c613bbu, 0x96557d82u, 0xf5914f81u, 0x421dac18u, 0xe8015338u}}
, .sourceIx = ty_w16
, .targetIx = ty_b
, .cost = 69 /* milli weight units */
}
,[FE_ADD] =
{ .tag = JET
, .jet = fe_add
, .cmr = {{0x9f0fa0f8u, 0x4d29d2c3u, 0x6d98baaau, 0xdd1aad0cu, 0x9bd4e1aeu, 0x7de98692u, 0xdd2a9c00u, 0xf40503d4u}}
, .sourceIx = ty_w512
, .targetIx = ty_w256
, .cost = 1408 /* milli weight units */
}
,[FE_INVERT] =
{ .tag = JET
, .jet = fe_invert
, .cmr = {{0x0148a606u, 0x5a45b7e9u, 0x564b2909u, 0x14073aadu, 0xbb895ddbu, 0xf6ff93f4u, 0x5e552c54u, 0x9d2e9900u}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 4008 /* milli weight units */
}
,[FE_IS_ODD] =
{ .tag = JET
, .jet = fe_is_odd
, .cmr = {{0xd6b7d544u, 0xe07df32au, 0x140d4315u, 0x4f4903d7u, 0x5c201d80u, 0x5264f2a4u, 0xfb8c10e4u, 0x16490c04u}}
, .sourceIx = ty_w256
, .targetIx = ty_b
, .cost = 311 /* milli weight units */
}
,[FE_IS_ZERO] =
{ .tag = JET
, .jet = fe_is_zero
, .cmr = {{0xaa0d4dc7u, 0xe1d9f02au, 0x38d1d365u, 0x8e1af7feu, 0x9c29dfbau, 0xd0a09438u, 0x1ae7e5cdu, 0x634b81e3u}}
, .sourceIx = ty_w256
, .targetIx = ty_b
, .cost = 299 /* milli weight units */
}
,[FE_MULTIPLY] =
{ .tag = JET
, .jet = fe_multiply
, .cmr = {{0xd9c74eb3u, 0x9b8bad28u, 0x21fdedfbu, 0x771fbff4u, 0xc905631au, 0xbc50f27cu, 0xbf547843u, 0xdd02560du}}
, .sourceIx = ty_w512
, .targetIx = ty_w256
, .cost = 1109 /* milli weight units */
}
,[FE_MULTIPLY_BETA] =
{ .tag = JET
, .jet = fe_multiply_beta
, .cmr = {{0x2f46cedau, 0xf4ae91f5u, 0x298ceb33u, 0x04ca9de8u, 0xccc416e6u, 0x7ba6f6a6u, 0x06a655b9u, 0x27929a0fu}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 755 /* milli weight units */
}
,[FE_NEGATE] =
{ .tag = JET
, .jet = fe_negate
, .cmr = {{0x6d39cae2u, 0x6d28087bu, 0x4a97cae2u, 0xd64790f4u, 0xade25895u, 0xc0a37d31u, 0x25834a13u, 0xc7670aceu}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 2187 /* milli weight units */
}
,[FE_NORMALIZE] =
{ .tag = JET
, .jet = fe_normalize
, .cmr = {{0x38c6be1du, 0xebb3fafdu, 0xaa318fbau, 0xe4f3abcau, 0x3e5e117bu, 0x01756a56u, 0x7df2940du, 0xe563866cu}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 2672 /* milli weight units */
}
,[FE_SQUARE] =
{ .tag = JET
, .jet = fe_square
, .cmr = {{0xfbc76256u, 0x79feac0au, 0xaf53c29bu, 0xdd9e8ac6u, 0x1d0ef2b8u, 0x0e493f3au, 0x602384f8u, 0x318b68bdu}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 800 /* milli weight units */
}
,[FE_SQUARE_ROOT] =
{ .tag = JET
, .jet = fe_square_root
, .cmr = {{0x86b3a133u, 0x34541b43u, 0x9ef24115u, 0x6f34def6u, 0x6d32baaau, 0xf6c6ca4fu, 0x6921580cu, 0x32e84918u}}
, .sourceIx = ty_w256
, .targetIx = ty_mw256
, .cost = 12716 /* milli weight units */
}
,[FULL_ADD_16] =
{ .tag = JET
, .jet = full_add_16
, .cmr = {{0xb64c4331u, 0x5b9456edu, 0x8070c1c8u, 0x29b7382du, 0xc85ec0deu, 0x754d4d9cu, 0xded3ce69u, 0x8c9a107bu}}
, .sourceIx = ty_pbw32
, .targetIx = ty_pbw16
, .cost = 93 /* milli weight units */
}
,[FULL_ADD_32] =
{ .tag = JET
, .jet = full_add_32
, .cmr = {{0x9185394du, 0xb2beb64du, 0xd08f8320u, 0x52f76fb0u, 0xe086cc5eu, 0xa4ed7ac8u, 0x5d22200du, 0xdb74ab26u}}
, .sourceIx = ty_pbw64
, .targetIx = ty_pbw32
, .cost = 93 /* milli weight units */
}
,[FULL_ADD_64] =
{ .tag = JET
, .jet = full_add_64
, .cmr = {{0xd38a1e79u, 0x3d39c4dau, 0xbb305444u, 0xb7078c09u, 0x247394a0u, 0xcc561927u, 0x585302b6u, 0x84a543b5u}}
, .sourceIx = ty_pbw128
, .targetIx = ty_pbw64
, .cost = 93 /* milli weight units */
}
,[FULL_ADD_8] =
{ .tag = JET
, .jet = full_add_8
, .cmr = {{0x993f6334u, 0x4f9c4ed3u, 0xaf291d71u, 0xf61fc409u, 0x47506821u, 0xeff700e5u, 0x21c1ecbbu, 0x32dfcc45u}}
, .sourceIx = ty_pbw16
, .targetIx = ty_pbw8
, .cost = 93 /* milli weight units */
}
,[FULL_DECREMENT_16] =
{ .tag = JET
, .jet = full_decrement_16
, .cmr = {{0x46f27340u, 0x31038ea6u, 0xf0e1da7fu, 0x9f04cca7u, 0x77e6c69fu, 0xffc11085u, 0x15868d51u, 0xedc8accbu}}
, .sourceIx = ty_pbw16
, .targetIx = ty_pbw16
, .cost = 109 /* milli weight units */
}
,[FULL_DECREMENT_32] =
{ .tag = JET
, .jet = full_decrement_32
, .cmr = {{0x22abbf3du, 0x6acf0b8cu, 0xb7f58f9cu, 0x7e927aa1u, 0xa1bb8fd0u, 0xb99623a1u, 0x1004ac53u, 0x6556ab02u}}
, .sourceIx = ty_pbw32
, .targetIx = ty_pbw32
, .cost = 109 /* milli weight units */
}
,[FULL_DECREMENT_64] =
{ .tag = JET
, .jet = full_decrement_64
, .cmr = {{0xd539aae2u, 0x2527d461u, 0x35461e40u, 0x59071e9du, 0x5b2fadfcu, 0xa13fb02au, 0xb5723e8au, 0x916a615cu}}
, .sourceIx = ty_pbw64
, .targetIx = ty_pbw64
, .cost = 109 /* milli weight units */
}
,[FULL_DECREMENT_8] =
{ .tag = JET
, .jet = full_decrement_8
, .cmr = {{0x3f636f40u, 0x169d072fu, 0x36820b1fu, 0x3f39c174u, 0x8624d9d5u, 0xfb957a8du, 0x4944f4fdu, 0x0d48597au}}
, .sourceIx = ty_pbw8
, .targetIx = ty_pbw8
, .cost = 109 /* milli weight units */
}
,[FULL_INCREMENT_16] =
{ .tag = JET
, .jet = full_increment_16
, .cmr = {{0x996422afu, 0xc52e28b1u, 0x25aa70b2u, 0xd07ca461u, 0x322fab6au, 0x45bb769du, 0xc12db2fau, 0x9af9bdbbu}}
, .sourceIx = ty_pbw16
, .targetIx = ty_pbw16
, .cost = 133 /* milli weight units */
}
,[FULL_INCREMENT_32] =
{ .tag = JET
, .jet = full_increment_32
, .cmr = {{0x1a5655fau, 0xe2af0ae6u, 0xa6acb587u, 0xa86c72bbu, 0x3088d765u, 0x6d253095u, 0x137c9ed0u, 0x448920bdu}}
, .sourceIx = ty_pbw32
, .targetIx = ty_pbw32
, .cost = 133 /* milli weight units */
}
,[FULL_INCREMENT_64] =
{ .tag = JET
, .jet = full_increment_64
, .cmr = {{0x807dc666u, 0xd3b1d3fdu, 0x65a40373u, 0xf6dfc6efu, 0x6419fa93u, 0x065c1a90u, 0x00def754u, 0x2c8ee8edu}}
, .sourceIx = ty_pbw64
, .targetIx = ty_pbw64
, .cost = 133 /* milli weight units */
}
,[FULL_INCREMENT_8] =
{ .tag = JET
, .jet = full_increment_8
, .cmr = {{0x1ffb9a76u, 0x2c99cb4du, 0x528cba4du, 0xc61f134fu, 0xdb4107e1u, 0xf49b076au, 0x5770f391u, 0x9595466cu}}
, .sourceIx = ty_pbw8
, .targetIx = ty_pbw8
, .cost = 133 /* milli weight units */
}
,[FULL_MULTIPLY_16] =
{ .tag = JET
, .jet = full_multiply_16
, .cmr = {{0x8f46faa9u, 0xec05e3d3u, 0xaeee3ec4u, 0x92ec534cu, 0xde6fc033u, 0x61e61999u, 0x4e8d0473u, 0xd6b09e5du}}
, .sourceIx = ty_w64
, .targetIx = ty_w32
, .cost = 138 /* milli weight units */
}
,[FULL_MULTIPLY_32] =
{ .tag = JET
, .jet = full_multiply_32
, .cmr = {{0x6c60021fu, 0x3b6f33e0u, 0x8ca42e4cu, 0x7e5acff4u, 0xcc7e0d69u, 0x86dfb355u, 0xabe05617u, 0x57f725cbu}}
, .sourceIx = ty_w128
, .targetIx = ty_w64
, .cost = 138 /* milli weight units */
}
,[FULL_MULTIPLY_64] =
{ .tag = JET
, .jet = full_multiply_64
, .cmr = {{0x05b27ce5u, 0x8ab086ddu, 0xb25a1cf9u, 0xe3091fdfu, 0x23214c54u, 0x31504032u, 0x4d4f6f10u, 0x953ed245u}}
, .sourceIx = ty_w256
, .targetIx = ty_w128
, .cost = 138 /* milli weight units */
}
,[FULL_MULTIPLY_8] =
{ .tag = JET
, .jet = full_multiply_8
, .cmr = {{0xcc22f308u, 0x18eb2d7bu, 0xe51142e6u, 0xb2c4eb64u, 0xad7c83d5u, 0xc195cddfu, 0x581bd975u, 0x6238146bu}}
, .sourceIx = ty_w32
, .targetIx = ty_w16
, .cost = 138 /* milli weight units */
}
,[FULL_SUBTRACT_16] =
{ .tag = JET
, .jet = full_subtract_16
, .cmr = {{0x416d747bu, 0xf01885b0u, 0x9ecb8f05u, 0x7e6b1540u, 0xe542fcdeu, 0x49a77461u, 0xc05ac730u, 0x845bdf8eu}}
, .sourceIx = ty_pbw32
, .targetIx = ty_pbw16
, .cost = 104 /* milli weight units */
}
,[FULL_SUBTRACT_32] =
{ .tag = JET
, .jet = full_subtract_32
, .cmr = {{0xb1bc9df5u, 0x702752b4u, 0xb30512aau, 0xef549c6bu, 0x0e824771u, 0x090b94efu, 0x9689bd4au, 0xe3aba881u}}
, .sourceIx = ty_pbw64
, .targetIx = ty_pbw32
, .cost = 104 /* milli weight units */
}
,[FULL_SUBTRACT_64] =
{ .tag = JET
, .jet = full_subtract_64
, .cmr = {{0xc244b536u, 0xd53c79a2u, 0xd45cdf8bu, 0x561bf510u, 0x22e5d581u, 0x98495078u, 0x4778de9eu, 0x6a90052fu}}
, .sourceIx = ty_pbw128
, .targetIx = ty_pbw64
, .cost = 104 /* milli weight units */
}
,[FULL_SUBTRACT_8] =
{ .tag = JET
, .jet = full_subtract_8
, .cmr = {{0x98a60f3au, 0x3198ca68u, 0x602aa0a5u, 0x23adc177u, 0xc366e803u, 0x319eee88u, 0x160ea3b0u, 0xefd7104cu}}
, .sourceIx = ty_pbw16
, .targetIx = ty_pbw8
, .cost = 104 /* milli weight units */
}
,[GE_IS_ON_CURVE] =
{ .tag = JET
, .jet = ge_is_on_curve
, .cmr = {{0xf3cda54au, 0x99b7011bu, 0xd488d31eu, 0xcafcac34u, 0x7a357b4du, 0xeb792b8cu, 0xfa3d00c7u, 0xb1097e4cu}}
, .sourceIx = ty_w512
, .targetIx = ty_b
, .cost = 768 /* milli weight units */
}
,[GE_NEGATE] =
{ .tag = JET
, .jet = ge_negate
, .cmr = {{0xa9fe3be6u, 0x70d15c78u, 0x9970ccf7u, 0x6ca869f8u, 0x0bbb772bu, 0x6ea0ae85u, 0x18d3a8d6u, 0xf883a642u}}
, .sourceIx = ty_w512
, .targetIx = ty_w512
, .cost = 1596 /* milli weight units */
}
,[GEJ_ADD] =
{ .tag = JET
, .jet = gej_add
, .cmr = {{0x93351359u, 0x9e036b4fu, 0xb8fc94ccu, 0x8cee437du, 0xa10f22cbu, 0xf8910e48u, 0xa5347faau, 0x363b404cu}}
, .sourceIx = ty_ppw512w256pw512w256
, .targetIx = ty_pw512w256
, .cost = 3274 /* milli weight units */
}
,[GEJ_DOUBLE] =
{ .tag = JET
, .jet = gej_double
, .cmr = {{0x08a1ce0au, 0x2479c6d1u, 0x424599fdu, 0x6ba91ed3u, 0xb5b95623u, 0x8ba1276du, 0xf51f069bu, 0xb247b18du}}
, .sourceIx = ty_pw512w256
, .targetIx = ty_pw512w256
, .cost = 1899 /* milli weight units */
}
,[GEJ_GE_ADD] =
{ .tag = JET
, .jet = gej_ge_add
, .cmr = {{0xfd6a62e5u, 0xee486d81u, 0x6d7d5078u, 0x3ae6c399u, 0x76bc7a3eu, 0x1967e84au, 0x3e3a1adcu, 0x645e45f8u}}
, .sourceIx = ty_ppw512w256w512
, .targetIx = ty_pw512w256
, .cost = 3004 /* milli weight units */
}
,[GEJ_GE_ADD_EX] =
{ .tag = JET
, .jet = gej_ge_add_ex
, .cmr = {{0xfd09fbc0u, 0xa6aca578u, 0x7661da11u, 0xeee93d4fu, 0xbbd74de1u, 0x1cf5316du, 0xb146423eu, 0xf890f118u}}
, .sourceIx = ty_ppw512w256w512
, .targetIx = ty_pw256pw512w256
, .cost = 2981 /* milli weight units */
}
,[GEJ_INFINITY] =
{ .tag = JET
, .jet = gej_infinity
, .cmr = {{0x738ff080u, 0xff208115u, 0x4e96cb1bu, 0xad2a74f6u, 0xe8eae338u, 0xcd56119cu, 0x5b156043u, 0x9089f8f1u}}
, .sourceIx = ty_u
, .targetIx = ty_pw512w256
, .cost = 1042 /* milli weight units */
}
,[GEJ_IS_INFINITY] =
{ .tag = JET
, .jet = gej_is_infinity
, .cmr = {{0x68e7f052u, 0xf0c5c9e2u, 0x6dcc3727u, 0xb80b00a4u, 0x7aaaa369u, 0xb3a96d18u, 0x7eb80a5cu, 0xaac29d98u}}
, .sourceIx = ty_pw512w256
, .targetIx = ty_b
, .cost = 1509 /* milli weight units */
}
,[GEJ_IS_ON_CURVE] =
{ .tag = JET
, .jet = gej_is_on_curve
, .cmr = {{0x5c64d06au, 0x8e631133u, 0xfe425dd1u, 0xac354e4eu, 0x8344dc2au, 0x21948275u, 0x9eeb557du, 0x8f3e87b4u}}
, .sourceIx = ty_pw512w256
, .targetIx = ty_b
, .cost = 1286 /* milli weight units */
}
,[GEJ_NEGATE] =
{ .tag = JET
, .jet = gej_negate
, .cmr = {{0x675eebfeu, 0x537f2774u, 0xeaafcb9fu, 0x0aa4e487u, 0x95765c18u, 0x6e2502b9u, 0x7dc30dbdu, 0x225d14f5u}}
, .sourceIx = ty_pw512w256
, .targetIx = ty_pw512w256
, .cost = 1596 /* milli weight units */
}
,[GEJ_NORMALIZE] =
{ .tag = JET
, .jet = gej_normalize
, .cmr = {{0x7c896342u, 0x1ef46d02u, 0xe8d576d6u, 0xbd060be8u, 0x8af5d3a3u, 0xd8a7a94cu, 0x99758297u, 0xd6064bd8u}}
, .sourceIx = ty_pw512w256
, .targetIx = ty_mw512
, .cost = 5931 /* milli weight units */
}
,[GEJ_RESCALE] =
{ .tag = JET
, .jet = gej_rescale
, .cmr = {{0x0258f6b5u, 0x8e2d5360u, 0x36e7ae59u, 0xc5450961u, 0xb4e82e09u, 0x5f3bb782u, 0x7cfbba59u, 0x19724144u}}
, .sourceIx = ty_ppw512w256w256
, .targetIx = ty_pw512w256
, .cost = 2462 /* milli weight units */
}
,[GEJ_X_EQUIV] =
{ .tag = JET
, .jet = gej_x_equiv
, .cmr = {{0xb71a68c6u, 0x1bea0141u, 0x554b9becu, 0x0697e9ceu, 0x9e447c2cu, 0x94c2f93fu, 0xbf10f66cu, 0x50f2256eu}}
, .sourceIx = ty_pw256pw512w256
, .targetIx = ty_b
, .cost = 1383 /* milli weight units */
}
,[GEJ_Y_IS_ODD] =
{ .tag = JET
, .jet = gej_y_is_odd
, .cmr = {{0x82df2426u, 0xe2ccc6f5u, 0xae2b4ac2u, 0x25e2a94cu, 0xf49cbe62u, 0xe64df4a9u, 0x33c116aeu, 0xb993e83du}}
, .sourceIx = ty_pw512w256
, .targetIx = ty_b
, .cost = 5506 /* milli weight units */
}
,[GENERATE] =
{ .tag = JET
, .jet = generate
, .cmr = {{0x90a34bddu, 0x0bee48f8u, 0x56d8ccf6u, 0x981a7264u, 0x8e3b5110u, 0x9b3bb255u, 0x20781410u, 0x577bfc81u}}
, .sourceIx = ty_w256
, .targetIx = ty_pw512w256
, .cost = 49026 /* milli weight units */
}
,[GENESIS_BLOCK_HASH] =
{ .tag = JET
, .jet = genesis_block_hash
, .cmr = {{0xb2a8fc83u, 0x998f358au, 0x0e0f493fu, 0x4ee85422u, 0xf64870eeu, 0x8b209b45u, 0x81cee85du, 0xffab5e83u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 143 /* milli weight units */
}
,[HIGH_16] =
{ .tag = JET
, .jet = high_16
, .cmr = {{0x1f52464du, 0xfa3874f6u, 0xda233b46u, 0x88799377u, 0xd8473265u, 0x8cda1b43u, 0x71498482u, 0x59cbd530u}}
, .sourceIx = ty_u
, .targetIx = ty_w16
, .cost = 57 /* milli weight units */
}
,[HIGH_32] =
{ .tag = JET
, .jet = high_32
, .cmr = {{0x60e0aa26u, 0xc8d7305cu, 0x4414b45du, 0xce3b29f1u, 0x073ec187u, 0x626082beu, 0x377234cfu, 0xd558c972u}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 57 /* milli weight units */
}
,[HIGH_64] =
{ .tag = JET
, .jet = high_64
, .cmr = {{0xaf1ad2bdu, 0x95ca2f4eu, 0x4862d4a3u, 0x9b8a4b79u, 0x805501bfu, 0x8a6d407eu, 0x972cf006u, 0x61c3a376u}}
, .sourceIx = ty_u
, .targetIx = ty_w64
, .cost = 57 /* milli weight units */
}
,[HIGH_8] =
{ .tag = JET
, .jet = high_8
, .cmr = {{0x3b30a52eu, 0x983eb1b8u, 0x613f3480u, 0x1b046449u, 0xa5e1ff32u, 0x27b096b9u, 0x3ca4ad9bu, 0x3f4bab82u}}
, .sourceIx = ty_u
, .targetIx = ty_w8
, .cost = 57 /* milli weight units */
}
,[INCREMENT_16] =
{ .tag = JET
, .jet = increment_16
, .cmr = {{0x7fcd357eu, 0x9774b602u, 0x8c27fbd4u, 0x481c2822u, 0xb745cf2cu, 0xb2ab8dcdu, 0xc7079f22u, 0x5cb15d6du}}
, .sourceIx = ty_w16
, .targetIx = ty_pbw16
, .cost = 133 /* milli weight units */
}
,[INCREMENT_32] =
{ .tag = JET
, .jet = increment_32
, .cmr = {{0x10268125u, 0xcb54b173u, 0x9e029f20u, 0x4d6ef0f7u, 0x216872fdu, 0x045eef08u, 0x961a79deu, 0xf889c69cu}}
, .sourceIx = ty_w32
, .targetIx = ty_pbw32
, .cost = 133 /* milli weight units */
}
,[INCREMENT_64] =
{ .tag = JET
, .jet = increment_64
, .cmr = {{0x728bec59u, 0xca50c233u, 0xd5b3da1du, 0x817cf83fu, 0x1112e2bau, 0xdaed0fa8u, 0xd4fcf122u, 0xc006299cu}}
, .sourceIx = ty_w64
, .targetIx = ty_pbw64
, .cost = 133 /* milli weight units */
}
,[INCREMENT_8] =
{ .tag = JET
, .jet = increment_8
, .cmr = {{0xefc24a38u, 0xa6ab373cu, 0xa7df08f9u, 0xe43cca03u, 0xcfd04282u, 0x7237f51eu, 0x4c707fb1u, 0x66f0ad25u}}
, .sourceIx = ty_w8
, .targetIx = ty_pbw8
, .cost = 133 /* milli weight units */
}
,[INPUT_AMOUNT] =
{ .tag = JET
, .jet = input_amount
, .cmr = {{0xa6779c5au, 0x1da895fbu, 0x09e3a76au, 0x016ed031u, 0x4c229053u, 0x8452d602u, 0x7d940f7bu, 0x51279879u}}
, .sourceIx = ty_w32
, .targetIx = ty_mpspbw256w256spbw256w64
, .cost = 185 /* milli weight units */
}
,[INPUT_AMOUNTS_HASH] =
{ .tag = JET
, .jet = input_amounts_hash
, .cmr = {{0xe7eafcf7u, 0x9d53f51cu, 0x9627793eu, 0x7149136bu, 0x0260211cu, 0x5091a614u, 0x947d588du, 0xc5f9c9e6u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 138 /* milli weight units */
}
,[INPUT_ANNEX_HASH] =
{ .tag = JET
, .jet = input_annex_hash
, .cmr = {{0xa69ff018u, 0x2d9e565fu, 0x35aa98d5u, 0x18f2b5b2u, 0xab41b82au, 0xe0cc6119u, 0x4d099f90u, 0xad96ff7bu}}
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
, .cost = 89 /* milli weight units */
}
,[INPUT_ANNEXES_HASH] =
{ .tag = JET
, .jet = input_annexes_hash
, .cmr = {{0xcb25456du, 0x25a14785u, 0x6a971c48u, 0x31fe5702u, 0x7278b9a6u, 0x00fd13f8u, 0xa437b4c4u, 0x522396eeu}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 125 /* milli weight units */
}
,[INPUT_ASSET] =
{ .tag = JET
, .jet = input_asset
, .cmr = {{0x266cb01cu, 0x76400972u, 0x200c92bau, 0xf8938533u, 0xfc4d65dau, 0x95c74459u, 0x7a93d9d3u, 0x998e10e7u}}
, .sourceIx = ty_w32
, .targetIx = ty_mspbw256w256
, .cost = 144 /* milli weight units */
}
,[INPUT_OUTPOINTS_HASH] =
{ .tag = JET
, .jet = input_outpoints_hash
, .cmr = {{0x4eeefaffu, 0x118c7774u, 0xf7afc5b4u, 0x5f90ff8eu, 0xb16eeb63u, 0x713c2298u, 0xd5c8799fu, 0xb8533b27u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 141 /* milli weight units */
}
,[INPUT_PEGIN] =
{ .tag = JET
, .jet = input_pegin
, .cmr = {{0xb5079696u, 0xda2b5be3u, 0x7283be5du, 0x33588f27u, 0x4fc836cfu, 0xf7c2f97fu, 0x99334386u, 0x4666c4fdu}}
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
, .cost = 162 /* milli weight units */
}
,[INPUT_PREV_OUTPOINT] =
{ .tag = JET
, .jet = input_prev_outpoint
, .cmr = {{0x86406b2cu, 0xfde4d95eu, 0x97ff9d67u, 0x502137b9u, 0x89117669u, 0x601349fdu, 0xba5f04e6u, 0xf1493a0du}}
, .sourceIx = ty_w32
, .targetIx = ty_mpw256w32
, .cost = 136 /* milli weight units */
}
,[INPUT_SCRIPT_HASH] =
{ .tag = JET
, .jet = input_script_hash
, .cmr = {{0x1720acabu, 0x93836788u, 0xd04053f2u, 0x75fd2737u, 0xa4f5c7a7u, 0x67835d3cu, 0x5bad522bu, 0x4c052e60u}}
, .sourceIx = ty_w32
, .targetIx = ty_mw256
, .cost = 152 /* milli weight units */
}
,[INPUT_SCRIPT_SIG_HASH] =
{ .tag = JET
, .jet = input_script_sig_hash
, .cmr = {{0xc26fa37cu, 0xef295bf8u, 0xa362c4c8u, 0x007df688u, 0x9ab78968u, 0xba43a1b3u, 0xf78006ceu, 0x44e44ccbu}}
, .sourceIx = ty_w32
, .targetIx = ty_mw256
, .cost = 156 /* milli weight units */
}
,[INPUT_SCRIPT_SIGS_HASH] =
{ .tag = JET
, .jet = input_script_sigs_hash
, .cmr = {{0xf792892eu, 0x016cdf32u, 0x49b9ba66u, 0x9ad23eb6u, 0x8db70dddu, 0x21c48ddfu, 0x10f0635fu, 0x2fdea008u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 111 /* milli weight units */
}
,[INPUT_SCRIPTS_HASH] =
{ .tag = JET
, .jet = input_scripts_hash
, .cmr = {{0x8d4ad3c0u, 0x71f30d6cu, 0x9e714d4au, 0x21f69001u, 0xaa3494bdu, 0x3f4e475eu, 0xf6cb8869u, 0x6c6da197u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 156 /* milli weight units */
}
,[INPUT_SEQUENCE] =
{ .tag = JET
, .jet = input_sequence
, .cmr = {{0xf971dbfeu, 0xef447450u, 0x0a2d3a3du, 0x36d2dba8u, 0x62ae872eu, 0xb3b0e356u, 0xf7c134e6u, 0xd255f5c4u}}
, .sourceIx = ty_w32
, .targetIx = ty_mw32
, .cost = 89 /* milli weight units */
}
,[INPUT_SEQUENCES_HASH] =
{ .tag = JET
, .jet = input_sequences_hash
, .cmr = {{0x4a82b87du, 0xc3ecf184u, 0x82a5038cu, 0xef1594a0u, 0xd95cae73u, 0x22d1a712u, 0x4464ab9cu, 0x3cb9ad33u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 117 /* milli weight units */
}
,[INPUT_UTXOS_HASH] =
{ .tag = JET
, .jet = input_utxos_hash
, .cmr = {{0x438da1ecu, 0x4378ff37u, 0x3dbadac7u, 0xdec29a53u, 0xa2c8919fu, 0x0a36aca1u, 0x1e2013dbu, 0x271ce8bdu}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 131 /* milli weight units */
}
,[INPUTS_HASH] =
{ .tag = JET
, .jet = inputs_hash
, .cmr = {{0x9684358eu, 0x5dd245c6u, 0xa809ef31u, 0x2a99695du, 0x6ea24036u, 0x0878648au, 0xc1f4a572u, 0xa4fb5e93u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 114 /* milli weight units */
}
,[INTERNAL_KEY] =
{ .tag = JET
, .jet = internal_key
, .cmr = {{0xb316dc70u, 0xd906020eu, 0x2d6b5bd6u, 0x66694ab7u, 0x39405413u, 0x272237dbu, 0x28dae142u, 0x8bef65b8u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 108 /* milli weight units */
}
,[IS_ONE_16] =
{ .tag = JET
, .jet = is_one_16
, .cmr = {{0x7cb3d4edu, 0xbf4640d2u, 0xe9c703c6u, 0x8acbbfc4u, 0x52efd60eu, 0xb1c2e04fu, 0x187e7d70u, 0xed457a39u}}
, .sourceIx = ty_w16
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[IS_ONE_32] =
{ .tag = JET
, .jet = is_one_32
, .cmr = {{0x91d74e95u, 0xef744e01u, 0xe56df6acu, 0x36df1839u, 0xab6c608cu, 0x7ab0afc1u, 0xfcc87eb5u, 0x0a27d799u}}
, .sourceIx = ty_w32
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[IS_ONE_64] =
{ .tag = JET
, .jet = is_one_64
, .cmr = {{0x7ddfc13au, 0x0543398eu, 0x8f0e07e6u, 0xca0544b5u, 0xff0a3ee8u, 0x3825b218u, 0xb3b8b0e4u, 0x2e9652a9u}}
, .sourceIx = ty_w64
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[IS_ONE_8] =
{ .tag = JET
, .jet = is_one_8
, .cmr = {{0xbcd4168eu, 0x02832dccu, 0xc9bfb57fu, 0x9a94d22cu, 0xc02dc74bu, 0xf458c817u, 0x3ea39e9eu, 0x16e60834u}}
, .sourceIx = ty_w8
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[IS_ZERO_16] =
{ .tag = JET
, .jet = is_zero_16
, .cmr = {{0xb516848cu, 0x3f282ca7u, 0xa80b1950u, 0x5e8fd138u, 0x80c993a9u, 0x4da59be7u, 0x723252bcu, 0x62a3c924u}}
, .sourceIx = ty_w16
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[IS_ZERO_32] =
{ .tag = JET
, .jet = is_zero_32
, .cmr = {{0x6991f026u, 0xaf707dd9u, 0x541de625u, 0x670f8320u, 0x800d5bbdu, 0x48047d44u, 0xc8ee0db1u, 0x33911936u}}
, .sourceIx = ty_w32
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[IS_ZERO_64] =
{ .tag = JET
, .jet = is_zero_64
, .cmr = {{0xe2f890c6u, 0x7d35dce2u, 0x4f7b2ca6u, 0x09af8bd2u, 0x35be6cd6u, 0x99970a43u, 0xc69bbbe2u, 0xf21d159cu}}
, .sourceIx = ty_w64
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[IS_ZERO_8] =
{ .tag = JET
, .jet = is_zero_8
, .cmr = {{0xa9c8c477u, 0xadd8a9f5u, 0x5852c51cu, 0xe1fbeb9au, 0x4c50c8f0u, 0xb63a55e8u, 0x924009a8u, 0xf59d3c69u}}
, .sourceIx = ty_w8
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[ISSUANCE] =
{ .tag = JET
, .jet = issuance
, .cmr = {{0xf84515cfu, 0x83eecbf0u, 0xfef6dcc1u, 0xcd4eb8e7u, 0x936e55b9u, 0xbd557f25u, 0x6375aeeeu, 0xf5db6a2du}}
, .sourceIx = ty_w32
, .targetIx = ty_mmb
, .cost = 89 /* milli weight units */
}
,[ISSUANCE_ASSET] =
{ .tag = JET
, .jet = issuance_asset
, .cmr = {{0xa2c2ffe6u, 0x2b7f0d1eu, 0xeda047a5u, 0x94e17ed2u, 0x50a0f1ceu, 0x8072e66cu, 0x8c2c666au, 0xe1d17d5bu}}
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
, .cost = 149 /* milli weight units */
}
,[ISSUANCE_ASSET_AMOUNT] =
{ .tag = JET
, .jet = issuance_asset_amount
, .cmr = {{0x77933819u, 0xa4c09104u, 0x3fa4a2f7u, 0x0f6a8562u, 0x7a644bb2u, 0x7281dd37u, 0x6829acfcu, 0xc60f8a68u}}
, .sourceIx = ty_w32
, .targetIx = ty_mmspbw256w64
, .cost = 142 /* milli weight units */
}
,[ISSUANCE_ASSET_AMOUNTS_HASH] =
{ .tag = JET
, .jet = issuance_asset_amounts_hash
, .cmr = {{0x76ce747bu, 0x3b4fd44eu, 0x8151196cu, 0x89cd385du, 0x3102975fu, 0x01361e77u, 0xae40dc6eu, 0x6b6a0c13u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 128 /* milli weight units */
}
,[ISSUANCE_ASSET_PROOF] =
{ .tag = JET
, .jet = issuance_asset_proof
, .cmr = {{0xa5317239u, 0x75b20852u, 0x00169a79u, 0xa33ab5e2u, 0xae294e8bu, 0xf351ec17u, 0x49f5307du, 0x06fc3cc8u}}
, .sourceIx = ty_w32
, .targetIx = ty_mw256
, .cost = 133 /* milli weight units */
}
,[ISSUANCE_BLINDING_ENTROPY_HASH] =
{ .tag = JET
, .jet = issuance_blinding_entropy_hash
, .cmr = {{0x3b4b13f3u, 0x2c82d2e6u, 0x2f8c1d65u, 0xadd8fca5u, 0x74a51b1eu, 0xb7e19765u, 0x72e57a46u, 0x51a6837bu}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 142 /* milli weight units */
}
,[ISSUANCE_ENTROPY] =
{ .tag = JET
, .jet = issuance_entropy
, .cmr = {{0xa616daefu, 0x37385050u, 0x866eaf5au, 0x01347a9bu, 0xaa84f1a2u, 0xf1a6e5c8u, 0x99770b00u, 0x0afecee3u}}
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
, .cost = 165 /* milli weight units */
}
,[ISSUANCE_RANGE_PROOFS_HASH] =
{ .tag = JET
, .jet = issuance_range_proofs_hash
, .cmr = {{0x77ba39d3u, 0xfa8948abu, 0x9bee093du, 0x2bedb75bu, 0x12d3fe7cu, 0x9168db4du, 0xf0f20937u, 0x9694a94fu}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 140 /* milli weight units */
}
,[ISSUANCE_TOKEN] =
{ .tag = JET
, .jet = issuance_token
, .cmr = {{0x7a73d442u, 0xc6671f7au, 0x043de208u, 0x889cfc13u, 0x13055f11u, 0x98625590u, 0x844023dau, 0xcf148fa8u}}
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
, .cost = 176 /* milli weight units */
}
,[ISSUANCE_TOKEN_AMOUNT] =
{ .tag = JET
, .jet = issuance_token_amount
, .cmr = {{0x5fc55682u, 0x707acd42u, 0xff2466dau, 0x71346082u, 0xb045616fu, 0x5fcc2b4bu, 0x305781aeu, 0x22eb034eu}}
, .sourceIx = ty_w32
, .targetIx = ty_mmspbw256w64
, .cost = 152 /* milli weight units */
}
,[ISSUANCE_TOKEN_AMOUNTS_HASH] =
{ .tag = JET
, .jet = issuance_token_amounts_hash
, .cmr = {{0xb0704a69u, 0xce0a3590u, 0xc4a1cdc0u, 0x872c53bcu, 0x9ef169e6u, 0x1b3fa37eu, 0x590dc8eau, 0x07d6db02u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 143 /* milli weight units */
}
,[ISSUANCE_TOKEN_PROOF] =
{ .tag = JET
, .jet = issuance_token_proof
, .cmr = {{0x3ff5e72eu, 0x0c539ee0u, 0x9dcb8dafu, 0xc0941c68u, 0x6ed4440cu, 0x8473cf03u, 0x0ad6ab91u, 0xecc2c530u}}
, .sourceIx = ty_w32
, .targetIx = ty_mw256
, .cost = 139 /* milli weight units */
}
,[ISSUANCES_HASH] =
{ .tag = JET
, .jet = issuances_hash
, .cmr = {{0x3498375du, 0x905b607cu, 0xd90a9fa1u, 0xb3dc8a87u, 0xda31c103u, 0x0a2a27eeu, 0xa99bb054u, 0x1eef4bbcu}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 124 /* milli weight units */
}
,[LE_16] =
{ .tag = JET
, .jet = le_16
, .cmr = {{0xd0269d47u, 0xd262ccb6u, 0x7e39eeb8u, 0x8f7ee0ecu, 0xd6f1f964u, 0x10252d59u, 0xce35cb87u, 0x1d09ca64u}}
, .sourceIx = ty_w32
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[LE_32] =
{ .tag = JET
, .jet = le_32
, .cmr = {{0x2cea9187u, 0x173a5070u, 0x4e93a631u, 0xd9cfb26au, 0xde50f6f1u, 0x9df4c359u, 0x15f49d22u, 0xa3ead4d5u}}
, .sourceIx = ty_w64
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[LE_64] =
{ .tag = JET
, .jet = le_64
, .cmr = {{0x092bb92eu, 0x9d8be5f3u, 0xcd88459eu, 0xca909e2au, 0x49af7ac9u, 0xf0df1159u, 0xc1ac1ac9u, 0x1bc51b0cu}}
, .sourceIx = ty_w128
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[LE_8] =
{ .tag = JET
, .jet = le_8
, .cmr = {{0x027d93d3u, 0xc247c390u, 0xe45ff324u, 0x08cc49a5u, 0xc17d55b0u, 0x4931daccu, 0x030a3a50u, 0x4a0e3c75u}}
, .sourceIx = ty_w16
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[LINEAR_COMBINATION_1] =
{ .tag = JET
, .jet = linear_combination_1
, .cmr = {{0x696c5f28u, 0xf9e759d9u, 0x6c2a0f99u, 0x0379fccfu, 0x084265f6u, 0x3393261du, 0x7249bba3u, 0x1dfa2441u}}
, .sourceIx = ty_ppw256pw512w256w256
, .targetIx = ty_pw512w256
, .cost = 83117 /* milli weight units */
}
,[LINEAR_VERIFY_1] =
{ .tag = JET
, .jet = linear_verify_1
, .cmr = {{0x9d0952bfu, 0x9997d851u, 0xa8cbbf8bu, 0xdf2d5ef4u, 0x108645cdu, 0xdff3f4f0u, 0x0d3824ddu, 0x1072752du}}
, .sourceIx = ty_pppw256w512w256w512
, .targetIx = ty_u
, .cost = 49791 /* milli weight units */
}
,[LOCK_TIME] =
{ .tag = JET
, .jet = lock_time
, .cmr = {{0x727e4a3eu, 0xf6f5bd8au, 0xb15ba270u, 0xe444e53eu, 0xa5f1fb37u, 0xbcf1b476u, 0x0edfb3cbu, 0x82ef3173u}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 59 /* milli weight units */
}
,[LOW_16] =
{ .tag = JET
, .jet = low_16
, .cmr = {{0xe3855bb4u, 0x645a0825u, 0xeaae0412u, 0x515a8b15u, 0xa37b305du, 0xed6f119au, 0x3f442531u, 0x297ab69cu}}
, .sourceIx = ty_u
, .targetIx = ty_w16
, .cost = 57 /* milli weight units */
}
,[LOW_32] =
{ .tag = JET
, .jet = low_32
, .cmr = {{0x75d2fb6bu, 0xe63b8b2cu, 0x3521123bu, 0x5ba77f78u, 0x1be9ff1cu, 0x1a75a8e2u, 0xceef6206u, 0xfb734589u}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 57 /* milli weight units */
}
,[LOW_64] =
{ .tag = JET
, .jet = low_64
, .cmr = {{0xea1249b3u, 0xe22e95f3u, 0xc6ff591eu, 0x872c03b6u, 0xf1b4a1d8u, 0xc045c5a3u, 0xbac7d921u, 0x272815b6u}}
, .sourceIx = ty_u
, .targetIx = ty_w64
, .cost = 57 /* milli weight units */
}
,[LOW_8] =
{ .tag = JET
, .jet = low_8
, .cmr = {{0x53e00b91u, 0x24d96014u, 0x7ab57244u, 0x5d373b42u, 0x0a222144u, 0x81bdec5eu, 0x6a3f05d5u, 0xab8e1984u}}
, .sourceIx = ty_u
, .targetIx = ty_w8
, .cost = 57 /* milli weight units */
}
,[LT_16] =
{ .tag = JET
, .jet = lt_16
, .cmr = {{0x11b4c033u, 0x2630bcc6u, 0xc6044c3fu, 0x887b2c50u, 0x39743f8au, 0xd908978eu, 0x7ba30a18u, 0xf05fecafu}}
, .sourceIx = ty_w32
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[LT_32] =
{ .tag = JET
, .jet = lt_32
, .cmr = {{0x04202245u, 0xd7590d5du, 0x9c68b84fu, 0x260fd36fu, 0x0fceb62au, 0xea204dd7u, 0xc5736bf6u, 0xb941b765u}}
, .sourceIx = ty_w64
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[LT_64] =
{ .tag = JET
, .jet = lt_64
, .cmr = {{0xe86f1edau, 0x2e39ef08u, 0x7e3f0316u, 0x62b8b1dau, 0x8df1a384u, 0x31e31bddu, 0x567f267fu, 0xa088e338u}}
, .sourceIx = ty_w128
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[LT_8] =
{ .tag = JET
, .jet = lt_8
, .cmr = {{0xa03e3cb8u, 0x4ba0c6d5u, 0xc9779392u, 0xe58f89a7u, 0x601cd525u, 0x49de6d75u, 0xff7155b1u, 0xf10a2e48u}}
, .sourceIx = ty_w16
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[MAJ_16] =
{ .tag = JET
, .jet = maj_16
, .cmr = {{0x298764b7u, 0xe8fb49b5u, 0xd9559b70u, 0x901f1a17u, 0x9656864eu, 0xeff3e269u, 0x21126f70u, 0x30f14a65u}}
, .sourceIx = ty_pw16w32
, .targetIx = ty_w16
, .cost = 133 /* milli weight units */
}
,[MAJ_32] =
{ .tag = JET
, .jet = maj_32
, .cmr = {{0xb8c17deau, 0x76e23b5du, 0x715cb00fu, 0x90113930u, 0xfeb91e86u, 0xc839411cu, 0x18e9ac86u, 0xfc8278c7u}}
, .sourceIx = ty_pw32w64
, .targetIx = ty_w32
, .cost = 133 /* milli weight units */
}
,[MAJ_64] =
{ .tag = JET
, .jet = maj_64
, .cmr = {{0x01d85ab4u, 0xbbc89ac3u, 0xa6f4ce55u, 0x64e1a842u, 0xd7303126u, 0x8c9eb98du, 0xf93e1209u, 0x420b4c0fu}}
, .sourceIx = ty_pw64w128
, .targetIx = ty_w64
, .cost = 133 /* milli weight units */
}
,[MAJ_8] =
{ .tag = JET
, .jet = maj_8
, .cmr = {{0x83ae95cbu, 0x1396c2c8u, 0x14b019f6u, 0x10371cb1u, 0x8f14b0f0u, 0x6eadc285u, 0xfaec3a4du, 0x5b229ae1u}}
, .sourceIx = ty_pw8w16
, .targetIx = ty_w8
, .cost = 133 /* milli weight units */
}
,[MAX_16] =
{ .tag = JET
, .jet = max_16
, .cmr = {{0xa17d86d1u, 0xdbb42f02u, 0xd6f77d73u, 0x5131b7a5u, 0x95861d24u, 0x955e9858u, 0x894b0476u, 0xee7468e3u}}
, .sourceIx = ty_w32
, .targetIx = ty_w16
, .cost = 98 /* milli weight units */
}
,[MAX_32] =
{ .tag = JET
, .jet = max_32
, .cmr = {{0x2d8db7e8u, 0xda9e7113u, 0xf338a32fu, 0x50e4b0feu, 0x55ab7eb3u, 0xcf4a0774u, 0xa8994e81u, 0x84f99839u}}
, .sourceIx = ty_w64
, .targetIx = ty_w32
, .cost = 98 /* milli weight units */
}
,[MAX_64] =
{ .tag = JET
, .jet = max_64
, .cmr = {{0x87e7bb87u, 0xb8d39951u, 0x6e239f5fu, 0x80ebfe2eu, 0x4e839046u, 0x975fac45u, 0x31cfaf84u, 0xb202ff89u}}
, .sourceIx = ty_w128
, .targetIx = ty_w64
, .cost = 98 /* milli weight units */
}
,[MAX_8] =
{ .tag = JET
, .jet = max_8
, .cmr = {{0xfae53c8cu, 0x421bd15cu, 0x6e311fd4u, 0xb107f64eu, 0x7a53e2a3u, 0xdc72ab0cu, 0xc14659a4u, 0x646a057bu}}
, .sourceIx = ty_w16
, .targetIx = ty_w8
, .cost = 98 /* milli weight units */
}
,[MEDIAN_16] =
{ .tag = JET
, .jet = median_16
, .cmr = {{0x1c9eb376u, 0x95d42f70u, 0x7193d487u, 0xe258a146u, 0x84a39b4du, 0x835c6bd3u, 0x4e33f70cu, 0x0055c1c6u}}
, .sourceIx = ty_pw16w32
, .targetIx = ty_w16
, .cost = 98 /* milli weight units */
}
,[MEDIAN_32] =
{ .tag = JET
, .jet = median_32
, .cmr = {{0x43669197u, 0x155021beu, 0x47d67b01u, 0xae70c125u, 0xa74b275cu, 0x46f4f60cu, 0xd2e754a5u, 0x697558dcu}}
, .sourceIx = ty_pw32w64
, .targetIx = ty_w32
, .cost = 98 /* milli weight units */
}
,[MEDIAN_64] =
{ .tag = JET
, .jet = median_64
, .cmr = {{0x18291ea2u, 0xe0884f11u, 0x29eb681fu, 0x689bd707u, 0x00db9e3fu, 0xa4ec0d3fu, 0xd184605au, 0x9643edb2u}}
, .sourceIx = ty_pw64w128
, .targetIx = ty_w64
, .cost = 98 /* milli weight units */
}
,[MEDIAN_8] =
{ .tag = JET
, .jet = median_8
, .cmr = {{0x01d819b8u, 0x33bf9973u, 0x6b1ad1fau, 0xdb9e8df6u, 0xfb94bdf6u, 0x267e165bu, 0xfb8085c4u, 0xd27170e3u}}
, .sourceIx = ty_pw8w16
, .targetIx = ty_w8
, .cost = 98 /* milli weight units */
}
,[MIN_16] =
{ .tag = JET
, .jet = min_16
, .cmr = {{0x6f65ef43u, 0x92f4554au, 0x1b90a62eu, 0xb4bb357eu, 0x468d5e85u, 0xe73b0183u, 0xfb366a75u, 0xaf0d5302u}}
, .sourceIx = ty_w32
, .targetIx = ty_w16
, .cost = 98 /* milli weight units */
}
,[MIN_32] =
{ .tag = JET
, .jet = min_32
, .cmr = {{0x24d0d083u, 0x63e5cbdau, 0xa9e0e0d2u, 0x3f6d4320u, 0xa0c49159u, 0x36c5126au, 0xc170745au, 0xe0736b3eu}}
, .sourceIx = ty_w64
, .targetIx = ty_w32
, .cost = 98 /* milli weight units */
}
,[MIN_64] =
{ .tag = JET
, .jet = min_64
, .cmr = {{0xde6c8c3fu, 0xaf2659fdu, 0xf52d44eau, 0xe4d38354u, 0xad097558u, 0xff8face2u, 0xe4a53717u, 0x38b473fbu}}
, .sourceIx = ty_w128
, .targetIx = ty_w64
, .cost = 98 /* milli weight units */
}
,[MIN_8] =
{ .tag = JET
, .jet = min_8
, .cmr = {{0xcb1e4f64u, 0xd8344859u, 0x0dbc5ad2u, 0x56884611u, 0xb1156b9au, 0xd235440fu, 0x44e66029u, 0x4efffc2cu}}
, .sourceIx = ty_w16
, .targetIx = ty_w8
, .cost = 98 /* milli weight units */
}
,[MODULO_16] =
{ .tag = JET
, .jet = modulo_16
, .cmr = {{0xb64fe4abu, 0xf684bc0cu, 0xb41c29ceu, 0x9dc2c5d8u, 0xefd52c46u, 0x3d08cb88u, 0xcf6c8488u, 0x90e280cdu}}
, .sourceIx = ty_w32
, .targetIx = ty_w16
, .cost = 138 /* milli weight units */
}
,[MODULO_32] =
{ .tag = JET
, .jet = modulo_32
, .cmr = {{0x34da4660u, 0xaeeafe01u, 0x529d8ce9u, 0xe1528423u, 0xcb870324u, 0x2e672c61u, 0x09fec5c1u, 0x1679506du}}
, .sourceIx = ty_w64
, .targetIx = ty_w32
, .cost = 138 /* milli weight units */
}
,[MODULO_64] =
{ .tag = JET
, .jet = modulo_64
, .cmr = {{0xcb1c3c88u, 0x452b06afu, 0xa97f37f9u, 0x553dbd28u, 0x9bda353au, 0x8bd1db52u, 0x73e4a3cbu, 0xc18f63cdu}}
, .sourceIx = ty_w128
, .targetIx = ty_w64
, .cost = 138 /* milli weight units */
}
,[MODULO_8] =
{ .tag = JET
, .jet = modulo_8
, .cmr = {{0xc977b579u, 0xa79313d2u, 0x1a0a7cf5u, 0x5dbf77eeu, 0xa32423b1u, 0xebf8dd48u, 0x970b4eb5u, 0x0ac296deu}}
, .sourceIx = ty_w16
, .targetIx = ty_w8
, .cost = 138 /* milli weight units */
}
,[MULTIPLY_16] =
{ .tag = JET
, .jet = multiply_16
, .cmr = {{0xc9e1cb83u, 0xb90ed4efu, 0xea73cd85u, 0xe75f9d04u, 0x23fed312u, 0x6f6471e4u, 0x4575c7f9u, 0x6c494cb1u}}
, .sourceIx = ty_w32
, .targetIx = ty_w32
, .cost = 87 /* milli weight units */
}
,[MULTIPLY_32] =
{ .tag = JET
, .jet = multiply_32
, .cmr = {{0x2a82b62fu, 0x5fb945c0u, 0x4eb78a48u, 0x9c28ae2fu, 0xa1376c49u, 0x64d9e206u, 0x262d13b0u, 0xd516c54au}}
, .sourceIx = ty_w64
, .targetIx = ty_w64
, .cost = 87 /* milli weight units */
}
,[MULTIPLY_64] =
{ .tag = JET
, .jet = multiply_64
, .cmr = {{0x4136a338u, 0xa82edd39u, 0xbf9f69acu, 0xad06a629u, 0xef5eeadcu, 0xdcd0a57fu, 0xca2ef245u, 0x966d892eu}}
, .sourceIx = ty_w128
, .targetIx = ty_w128
, .cost = 87 /* milli weight units */
}
,[MULTIPLY_8] =
{ .tag = JET
, .jet = multiply_8
, .cmr = {{0x2582993du, 0x80b98ed1u, 0xe06d3013u, 0xb93c412cu, 0xc2343a79u, 0xc9a72538u, 0x4ca11811u, 0xd0b9080bu}}
, .sourceIx = ty_w16
, .targetIx = ty_w16
, .cost = 87 /* milli weight units */
}
,[NEGATE_16] =
{ .tag = JET
, .jet = negate_16
, .cmr = {{0xdfb13260u, 0x3d541a98u, 0x948e162fu, 0xc958b055u, 0xb49e6006u, 0x850be667u, 0xad0c94bfu, 0xa4512155u}}
, .sourceIx = ty_w16
, .targetIx = ty_pbw16
, .cost = 109 /* milli weight units */
}
,[NEGATE_32] =
{ .tag = JET
, .jet = negate_32
, .cmr = {{0xd81eb9d8u, 0x8a19d914u, 0x030e3186u, 0x38efd853u, 0x5bd965e9u, 0x5136fca4u, 0x98d21d30u, 0x55302708u}}
, .sourceIx = ty_w32
, .targetIx = ty_pbw32
, .cost = 109 /* milli weight units */
}
,[NEGATE_64] =
{ .tag = JET
, .jet = negate_64
, .cmr = {{0x38d74e41u, 0xe4670444u, 0xb9e78680u, 0x2e174343u, 0x8846220au, 0x60accdd9u, 0xc66225c4u, 0x7e470553u}}
, .sourceIx = ty_w64
, .targetIx = ty_pbw64
, .cost = 109 /* milli weight units */
}
,[NEGATE_8] =
{ .tag = JET
, .jet = negate_8
, .cmr = {{0xbcc252b8u, 0x13f2197eu, 0xbd25a9cbu, 0x913f2697u, 0xcdd08a61u, 0x68936a0cu, 0x65fc897eu, 0x33bbfdfcu}}
, .sourceIx = ty_w8
, .targetIx = ty_pbw8
, .cost = 109 /* milli weight units */
}
,[NEW_ISSUANCE_CONTRACT] =
{ .tag = JET
, .jet = new_issuance_contract
, .cmr = {{0x8752ac81u, 0x516dd080u, 0x9d9e6b71u, 0xe352fc4bu, 0xbe0a2c26u, 0xc36754ddu, 0x48baccc6u, 0x42413826u}}
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
, .cost = 192 /* milli weight units */
}
,[NONCE_HASH] =
{ .tag = JET
, .jet = nonce_hash
, .cmr = {{0x3588c8e3u, 0xd0b313bcu, 0xef26c231u, 0xccda6ae1u, 0x4cbdbc95u, 0xd7272245u, 0x10589200u, 0x0685f722u}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256mspbw256w256
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 433 /* milli weight units */
}
,[NUM_INPUTS] =
{ .tag = JET
, .jet = num_inputs
, .cmr = {{0x09028c91u, 0xe945b67cu, 0x69acac89u, 0xbb9d660du, 0x7fa21ac7u, 0x48177863u, 0x40df0864u, 0x03d85ebdu}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 60 /* milli weight units */
}
,[NUM_OUTPUTS] =
{ .tag = JET
, .jet = num_outputs
, .cmr = {{0x43d55973u, 0xe964c063u, 0x0e752e29u, 0x156961d3u, 0x0276617du, 0x45362b2au, 0x7950fb28u, 0x54ea0d24u}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 60 /* milli weight units */
}
,[ONE_16] =
{ .tag = JET
, .jet = one_16
, .cmr = {{0xf6a14c50u, 0x6190cc5du, 0xbdfb2492u, 0x027a4de3u, 0x79dd2d57u, 0x85e0512du, 0x43faeb1cu, 0xd2512814u}}
, .sourceIx = ty_u
, .targetIx = ty_w16
, .cost = 53 /* milli weight units */
}
,[ONE_32] =
{ .tag = JET
, .jet = one_32
, .cmr = {{0xc42b70b5u, 0x2aa3978cu, 0x2882b8c2u, 0x32364be8u, 0xf48ed73du, 0x33086be7u, 0x2c38f1c3u, 0x66f43502u}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 53 /* milli weight units */
}
,[ONE_64] =
{ .tag = JET
, .jet = one_64
, .cmr = {{0x40c317bcu, 0x23ce5a48u, 0x6ae32505u, 0xa38ad17au, 0x84479a10u, 0x86715b92u, 0xac2960bdu, 0xfe0edbc9u}}
, .sourceIx = ty_u
, .targetIx = ty_w64
, .cost = 53 /* milli weight units */
}
,[ONE_8] =
{ .tag = JET
, .jet = one_8
, .cmr = {{0xc0d351bau, 0x4126b60eu, 0x888dcc1eu, 0x59f12398u, 0xb4d85efdu, 0x18fe3da4u, 0x74a2966bu, 0x04a61317u}}
, .sourceIx = ty_u
, .targetIx = ty_w8
, .cost = 53 /* milli weight units */
}
,[OR_16] =
{ .tag = JET
, .jet = or_16
, .cmr = {{0x58d709e8u, 0xaaf412ffu, 0x2799547au, 0xc9144a79u, 0x77ce49ccu, 0x8e9563d4u, 0x5d6800adu, 0x5e4eff2eu}}
, .sourceIx = ty_w32
, .targetIx = ty_w16
, .cost = 133 /* milli weight units */
}
,[OR_32] =
{ .tag = JET
, .jet = or_32
, .cmr = {{0x8e0378d2u, 0x41c14237u, 0xd218a48fu, 0xfd045163u, 0x4de563a4u, 0xd4ba7c7au, 0xc8c0428du, 0x33d1678eu}}
, .sourceIx = ty_w64
, .targetIx = ty_w32
, .cost = 133 /* milli weight units */
}
,[OR_64] =
{ .tag = JET
, .jet = or_64
, .cmr = {{0xc03abc73u, 0x13ffbd09u, 0xc869b4a8u, 0xfd610c94u, 0x12d05a94u, 0x2609afafu, 0xbc8ba607u, 0xb45db8d8u}}
, .sourceIx = ty_w128
, .targetIx = ty_w64
, .cost = 133 /* milli weight units */
}
,[OR_8] =
{ .tag = JET
, .jet = or_8
, .cmr = {{0x0a28c7f0u, 0xd0944258u, 0xb1a04900u, 0xf0338207u, 0x31efeab6u, 0x44102c7au, 0xa545aa32u, 0x76bd2273u}}
, .sourceIx = ty_w16
, .targetIx = ty_w8
, .cost = 133 /* milli weight units */
}
,[OUTPOINT_HASH] =
{ .tag = JET
, .jet = outpoint_hash
, .cmr = {{0x61877914u, 0x0aa7c32fu, 0x8ce40e11u, 0x06ec27e8u, 0x4ebf705au, 0x7f1aea08u, 0x726a91e5u, 0x8943d722u}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256pmw256pw256w32
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 427 /* milli weight units */
}
,[OUTPUT_AMOUNT] =
{ .tag = JET
, .jet = output_amount
, .cmr = {{0x2a438d50u, 0x8bb93cfcu, 0x86cd13c7u, 0x5676f9ddu, 0x9fd84285u, 0x45bef2e7u, 0xe8578bc3u, 0x81264298u}}
, .sourceIx = ty_w32
, .targetIx = ty_mpspbw256w256spbw256w64
, .cost = 166 /* milli weight units */
}
,[OUTPUT_AMOUNTS_HASH] =
{ .tag = JET
, .jet = output_amounts_hash
, .cmr = {{0xf31ade56u, 0xdc654cd9u, 0x627e5fb8u, 0xdfe779fau, 0x9e450d69u, 0xcc849149u, 0xeeabe7adu, 0x1b249d50u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 127 /* milli weight units */
}
,[OUTPUT_ASSET] =
{ .tag = JET
, .jet = output_asset
, .cmr = {{0x5a9f3cbcu, 0xc3639359u, 0x3db80d0cu, 0xa4bde455u, 0x5a7d7cebu, 0xbd0abdcfu, 0x73af0426u, 0x4d7657d5u}}
, .sourceIx = ty_w32
, .targetIx = ty_mspbw256w256
, .cost = 142 /* milli weight units */
}
,[OUTPUT_IS_FEE] =
{ .tag = JET
, .jet = output_is_fee
, .cmr = {{0x45b8c5eau, 0x18bf697au, 0x97c342eau, 0x75e32f5bu, 0x93c0a2b1u, 0x27e05133u, 0xbdb8f2b9u, 0x1564ebc9u}}
, .sourceIx = ty_w32
, .targetIx = ty_mb
, .cost = 162 /* milli weight units */
}
,[OUTPUT_NONCE] =
{ .tag = JET
, .jet = output_nonce
, .cmr = {{0xb3954e56u, 0xe7ba56e7u, 0xe4ad212au, 0x6874b05eu, 0xd53bbf05u, 0x487d60dau, 0x3bfe3cbbu, 0x747a9e15u}}
, .sourceIx = ty_w32
, .targetIx = ty_mmspbw256w256
, .cost = 74 /* milli weight units */
}
,[OUTPUT_NONCES_HASH] =
{ .tag = JET
, .jet = output_nonces_hash
, .cmr = {{0x3d366f30u, 0xec755568u, 0xbc0e1d69u, 0xa9f9a8afu, 0x98ed8ad5u, 0x99afb349u, 0x53f1a13eu, 0x6ed03e42u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 111 /* milli weight units */
}
,[OUTPUT_NULL_DATUM] =
{ .tag = JET
, .jet = output_null_datum
, .cmr = {{0x3d8c4c85u, 0x25ad238fu, 0xb618a0d0u, 0x4a6bc36eu, 0xe14a9908u, 0x8cb558dbu, 0x2fd2ac9eu, 0x5673b67bu}}
, .sourceIx = ty_w64
, .targetIx = ty_mmspw2w256sbw4
, .cost = 73 /* milli weight units */
}
,[OUTPUT_RANGE_PROOF] =
{ .tag = JET
, .jet = output_range_proof
, .cmr = {{0x97e5dbf2u, 0x5d0049e4u, 0x2388967du, 0x4459b6bbu, 0xb2128d1bu, 0x7fd23c6eu, 0xf7aa9f8du, 0xfcacd524u}}
, .sourceIx = ty_w32
, .targetIx = ty_mw256
, .cost = 233 /* milli weight units */
}
,[OUTPUT_RANGE_PROOFS_HASH] =
{ .tag = JET
, .jet = output_range_proofs_hash
, .cmr = {{0x1ea053e5u, 0xc8aceeabu, 0x93aa33f7u, 0x7542d2d6u, 0x829c3862u, 0x9a4be464u, 0xf10c8a56u, 0x9faeb84cu}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 111 /* milli weight units */
}
,[OUTPUT_SCRIPT_HASH] =
{ .tag = JET
, .jet = output_script_hash
, .cmr = {{0xd72b685eu, 0x74c70d0eu, 0x562ec0f0u, 0x4ff06298u, 0x61a5a212u, 0xdfa83cf8u, 0x8b0ff733u, 0x81e69ea1u}}
, .sourceIx = ty_w32
, .targetIx = ty_mw256
, .cost = 130 /* milli weight units */
}
,[OUTPUT_SCRIPTS_HASH] =
{ .tag = JET
, .jet = output_scripts_hash
, .cmr = {{0xb399b2dcu, 0x2afa8560u, 0xf882d9d5u, 0xc834b685u, 0xef95e512u, 0x0deb8cb7u, 0x944b648bu, 0x57e5aff5u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 122 /* milli weight units */
}
,[OUTPUT_SURJECTION_PROOF] =
{ .tag = JET
, .jet = output_surjection_proof
, .cmr = {{0x7c76340au, 0x1748f461u, 0x89d0e99du, 0x5e725293u, 0x409474bbu, 0x4522abc2u, 0xd9255fa4u, 0x5548de6fu}}
, .sourceIx = ty_w32
, .targetIx = ty_mw256
, .cost = 127 /* milli weight units */
}
,[OUTPUT_SURJECTION_PROOFS_HASH] =
{ .tag = JET
, .jet = output_surjection_proofs_hash
, .cmr = {{0x6a8e53abu, 0x3659fb36u, 0x864411beu, 0xcd0cc68cu, 0xea87b697u, 0x80619e9du, 0x33f32c2bu, 0x4bfc9e82u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 163 /* milli weight units */
}
,[OUTPUTS_HASH] =
{ .tag = JET
, .jet = outputs_hash
, .cmr = {{0x6e59e23eu, 0x42b5c119u, 0xc287d1c0u, 0x5ea3409bu, 0x8cc86321u, 0x456029bbu, 0x6e315839u, 0x641aaf50u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 136 /* milli weight units */
}
,[PARSE_LOCK] =
{ .tag = JET
, .jet = parse_lock
, .cmr = {{0x1383d328u, 0xa40bc634u, 0x2174baafu, 0x9a390932u, 0xc1fe4f2fu, 0x4a8ec7fdu, 0x218babf1u, 0x805fb7e5u}}
, .sourceIx = ty_w32
, .targetIx = ty_sw32w32
, .cost = 84 /* milli weight units */
}
,[PARSE_SEQUENCE] =
{ .tag = JET
, .jet = parse_sequence
, .cmr = {{0xc9617769u, 0x106d45a3u, 0x70f293aau, 0x222ee6b4u, 0x1502e274u, 0xce41b905u, 0x9c9dde89u, 0x73cd80c7u}}
, .sourceIx = ty_w32
, .targetIx = ty_msw16w16
, .cost = 82 /* milli weight units */
}
,[POINT_VERIFY_1] =
{ .tag = JET
, .jet = point_verify_1
, .cmr = {{0x869447dcu, 0x82a9edf8u, 0xb144a3eeu, 0xbafd7a5du, 0xcb70f458u, 0x3d95d785u, 0xdc01fdb3u, 0x61481ed5u}}
, .sourceIx = ty_pppw256pbw256w256pbw256
, .targetIx = ty_u
, .cost = 56153 /* milli weight units */
}
,[REISSUANCE_BLINDING] =
{ .tag = JET
, .jet = reissuance_blinding
, .cmr = {{0x3280f4e8u, 0xfa64aa3fu, 0xf616d93bu, 0x6dd668e9u, 0xa969c071u, 0xf9ad3934u, 0x7385aadau, 0x3fe0ffbeu}}
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
, .cost = 82 /* milli weight units */
}
,[REISSUANCE_ENTROPY] =
{ .tag = JET
, .jet = reissuance_entropy
, .cmr = {{0xf7f9a085u, 0xffd44fd6u, 0x199e165eu, 0x3110910du, 0x41460700u, 0x22f08504u, 0x9ea02651u, 0xb417dc98u}}
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
, .cost = 179 /* milli weight units */
}
,[SCALAR_ADD] =
{ .tag = JET
, .jet = scalar_add
, .cmr = {{0x47fad94fu, 0xfa741b30u, 0x2234805eu, 0x5da543ceu, 0xcc8e0bf8u, 0x61c607e3u, 0xd25a842cu, 0xe61e06dau}}
, .sourceIx = ty_w512
, .targetIx = ty_w256
, .cost = 862 /* milli weight units */
}
,[SCALAR_INVERT] =
{ .tag = JET
, .jet = scalar_invert
, .cmr = {{0x6d59edd6u, 0xa82f2085u, 0xa79e822bu, 0x1cd02143u, 0x1d80e3f3u, 0x635b255bu, 0xc79abd47u, 0x21f82fdbu}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 3853 /* milli weight units */
}
,[SCALAR_IS_ZERO] =
{ .tag = JET
, .jet = scalar_is_zero
, .cmr = {{0xb21881e2u, 0xbdfa6af0u, 0x05f1bd1eu, 0x36e04211u, 0x27484714u, 0x77e2089fu, 0xc1e351c7u, 0x1502c5cau}}
, .sourceIx = ty_w256
, .targetIx = ty_b
, .cost = 323 /* milli weight units */
}
,[SCALAR_MULTIPLY] =
{ .tag = JET
, .jet = scalar_multiply
, .cmr = {{0xe6f6b655u, 0x01da00b2u, 0x7b1f4efeu, 0x31c2712fu, 0x31d1b176u, 0xa9ccdd0cu, 0xf00c587au, 0xf12a05fdu}}
, .sourceIx = ty_w512
, .targetIx = ty_w256
, .cost = 1070 /* milli weight units */
}
,[SCALAR_MULTIPLY_LAMBDA] =
{ .tag = JET
, .jet = scalar_multiply_lambda
, .cmr = {{0x4ddf8fcbu, 0x58ffae7bu, 0x3aa6bc52u, 0xffae76adu, 0xa337045bu, 0xa00980f5u, 0x2158099bu, 0x539a942eu}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 736 /* milli weight units */
}
,[SCALAR_NEGATE] =
{ .tag = JET
, .jet = scalar_negate
, .cmr = {{0x007fba3du, 0x50deb603u, 0xdd233e94u, 0x63117d49u, 0x36033a50u, 0xf6822190u, 0x0c931953u, 0xf82c1603u}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 726 /* milli weight units */
}
,[SCALAR_NORMALIZE] =
{ .tag = JET
, .jet = scalar_normalize
, .cmr = {{0xbbfa235au, 0x9576d3d6u, 0xeb82f3c9u, 0x4427694fu, 0xc5d97a90u, 0xd4c4ee32u, 0xcd80d0dbu, 0xad99d93au}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 740 /* milli weight units */
}
,[SCALAR_SQUARE] =
{ .tag = JET
, .jet = scalar_square
, .cmr = {{0xa5cb2226u, 0xa09f26aau, 0x53f15480u, 0x34cd58ccu, 0x631bea69u, 0x72658a9cu, 0x55698c39u, 0x7f0a845bu}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 822 /* milli weight units */
}
,[SCALE] =
{ .tag = JET
, .jet = scale
, .cmr = {{0xa723538cu, 0x2d33f767u, 0x9aa948ddu, 0x96407c3du, 0xddaf02acu, 0x27ff2ec2u, 0x8d4cc27eu, 0xeafe6bc3u}}
, .sourceIx = ty_pw256pw512w256
, .targetIx = ty_pw512w256
, .cost = 75458 /* milli weight units */
}
,[SCRIPT_CMR] =
{ .tag = JET
, .jet = script_cmr
, .cmr = {{0xb344cd4cu, 0xbb595286u, 0xafab2c19u, 0xe2f0ba06u, 0x8bbeafe5u, 0xa3b14f0eu, 0xe57a5ddeu, 0xda111c45u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 110 /* milli weight units */
}
,[SHA_256_BLOCK] =
{ .tag = JET
, .jet = sha_256_block
, .cmr = {{0xd3e3c69au, 0xed822b24u, 0xf94614f2u, 0xc2d7cb39u, 0x1d3a1717u, 0xf13de9d5u, 0x89cf0a14u, 0x624668deu}}
, .sourceIx = ty_pw256w512
, .targetIx = ty_w256
, .cost = 1046 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_1] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_1
, .cmr = {{0x4aafee24u, 0x56b51e53u, 0x622c9f82u, 0xc3e46c91u, 0xb2d79b65u, 0x9c54f5fau, 0x671b04d6u, 0x0a42c56au}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w8
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 454 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_128] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_128
, .cmr = {{0xae960780u, 0x6cc3dd3au, 0xe45423beu, 0x2422696au, 0xf4e9adfcu, 0xc5aca88eu, 0xa796c6fbu, 0x64ef2486u}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w1Ki
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 401 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_16] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_16
, .cmr = {{0x35912a51u, 0xd9badb3fu, 0x8847eddcu, 0x53c8b2ebu, 0xdb62dd3bu, 0x497fe0b4u, 0x7726c0c7u, 0x029ecd89u}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w128
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 340 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_2] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_2
, .cmr = {{0x86fafa03u, 0x8b9d86f7u, 0xb55e5ad7u, 0x318b140fu, 0x562891c9u, 0x114ad0cau, 0xcb9953c6u, 0xa2edb994u}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w16
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 576 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_256] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_256
, .cmr = {{0xe7c6521bu, 0x4e3adbbbu, 0x34df286au, 0x41dca137u, 0xf6a1c3eeu, 0x406fd596u, 0x28714db1u, 0x074662a5u}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w2Ki
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 572 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_32] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_32
, .cmr = {{0x16fadfc2u, 0xfb9e7383u, 0x85bf0819u, 0x14afc974u, 0x30edce32u, 0x0e1203acu, 0xc20549dbu, 0x89a1c29eu}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w256
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 326 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_4] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_4
, .cmr = {{0xb7a30aecu, 0x7d6d78adu, 0x8357a4c6u, 0x2be7bf6du, 0xe07e4401u, 0x06b53ccbu, 0xf9ef4102u, 0x2f03d7e2u}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w32
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 570 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_512] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_512
, .cmr = {{0xb319e284u, 0x6ad9ce46u, 0xe8b478c6u, 0x47007bbdu, 0x4b3a1a45u, 0xbd2ee479u, 0x96fa0a2au, 0xf40ebd52u}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w4Ki
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 559 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_64] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_64
, .cmr = {{0x7514d908u, 0x1786024du, 0x71189915u, 0xb005d7c2u, 0x21748e48u, 0x2fd816b8u, 0x81145be2u, 0x9797b4ddu}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w512
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 475 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_8] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_8
, .cmr = {{0xb0b7131au, 0x4112c653u, 0x06e22ad3u, 0x54704e3eu, 0xc2d74443u, 0x4f4a4d6au, 0xe8bcfd35u, 0x39c10adfu}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w64
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 330 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_BUFFER_511] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_buffer_511
, .cmr = {{0xc288e0d1u, 0xfdddb9e0u, 0xaef4fa05u, 0x9cc8830eu, 0x7125a610u, 0xb6a3a71eu, 0x8aa49669u, 0x6ea773fbu}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256pmw2Kipmw1Kipmw512pmw256pmw128pmw64pmw32pmw16mw8
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 412 /* milli weight units */
}
,[SHA_256_CTX_8_FINALIZE] =
{ .tag = JET
, .jet = sha_256_ctx_8_finalize
, .cmr = {{0x5968672bu, 0x01c72f8eu, 0x84fac9d1u, 0x7e1e9df8u, 0xf8786b4bu, 0x4704044du, 0xd57eaf77u, 0x3603888fu}}
, .sourceIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .targetIx = ty_w256
, .cost = 1205 /* milli weight units */
}
,[SHA_256_CTX_8_INIT] =
{ .tag = JET
, .jet = sha_256_ctx_8_init
, .cmr = {{0x79a02955u, 0x61f6554fu, 0x04cb94c9u, 0x8968d1bdu, 0x6966fc97u, 0x8553832bu, 0x20f75c2bu, 0x155659bau}}
, .sourceIx = ty_u
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 237 /* milli weight units */
}
,[SHA_256_IV] =
{ .tag = JET
, .jet = sha_256_iv
, .cmr = {{0x90251f75u, 0xabf9378fu, 0xfa815e74u, 0x2c894a38u, 0xb942f28cu, 0xffe9a447u, 0xcabbe6ddu, 0x2c2cd026u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 107 /* milli weight units */
}
,[SIG_ALL_HASH] =
{ .tag = JET
, .jet = sig_all_hash
, .cmr = {{0x3604f17cu, 0x73718653u, 0x1220da2cu, 0x7c19281du, 0x251a510eu, 0x732dbc4au, 0xb5a54787u, 0x7cb5ff18u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 135 /* milli weight units */
}
,[SOME_16] =
{ .tag = JET
, .jet = some_16
, .cmr = {{0xcecb74b8u, 0x3135f534u, 0x0b6d88f3u, 0xb712f150u, 0x4d2e5032u, 0x867fa7b9u, 0xa2c4b424u, 0xd965c78eu}}
, .sourceIx = ty_w16
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[SOME_32] =
{ .tag = JET
, .jet = some_32
, .cmr = {{0x0ce7cab8u, 0x0f07b12du, 0x9c9b94c4u, 0x71d958a1u, 0xe72414b9u, 0x348c1c53u, 0xe0324c2bu, 0x89de26f8u}}
, .sourceIx = ty_w32
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[SOME_64] =
{ .tag = JET
, .jet = some_64
, .cmr = {{0x2fe1b408u, 0x34ae9f5cu, 0xcbcfa8e7u, 0x919eb11cu, 0x71468891u, 0x7110aeeau, 0x8db778d8u, 0x5da4e643u}}
, .sourceIx = ty_w64
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[SOME_8] =
{ .tag = JET
, .jet = some_8
, .cmr = {{0x33d958a6u, 0x8c24f63bu, 0xe7b00699u, 0x39ccfc22u, 0xb6a43480u, 0x525f7856u, 0x70edd134u, 0xff24f6d0u}}
, .sourceIx = ty_w8
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[SUBTRACT_16] =
{ .tag = JET
, .jet = subtract_16
, .cmr = {{0x7d22f499u, 0x7a66d174u, 0x31c23481u, 0xf40a44d3u, 0xb45f9d8au, 0xbf549632u, 0x5452771au, 0x87c77c6bu}}
, .sourceIx = ty_w32
, .targetIx = ty_pbw16
, .cost = 109 /* milli weight units */
}
,[SUBTRACT_32] =
{ .tag = JET
, .jet = subtract_32
, .cmr = {{0x5b3be7fdu, 0x8ab01431u, 0x49c1d9f9u, 0xd88a9d99u, 0xea70fdc0u, 0x86bcf388u, 0xbf9f4dd9u, 0xe12d173cu}}
, .sourceIx = ty_w64
, .targetIx = ty_pbw32
, .cost = 109 /* milli weight units */
}
,[SUBTRACT_64] =
{ .tag = JET
, .jet = subtract_64
, .cmr = {{0x17653edbu, 0xddea93a4u, 0xc20ff359u, 0xadc9975bu, 0x7c2abf8cu, 0xf32a1bc1u, 0x47e2c900u, 0x25bcfd19u}}
, .sourceIx = ty_w128
, .targetIx = ty_pbw64
, .cost = 109 /* milli weight units */
}
,[SUBTRACT_8] =
{ .tag = JET
, .jet = subtract_8
, .cmr = {{0x778649f8u, 0x3935cd3fu, 0xfc04f6c6u, 0x620a3396u, 0x5d0ef1ddu, 0x17e7b50fu, 0xa41076d8u, 0xad876b1du}}
, .sourceIx = ty_w16
, .targetIx = ty_pbw8
, .cost = 109 /* milli weight units */
}
,[TAP_ENV_HASH] =
{ .tag = JET
, .jet = tap_env_hash
, .cmr = {{0x1634e5c7u, 0x4c212624u, 0x8d5d117cu, 0x53ee4fceu, 0x83aea076u, 0x6021969bu, 0x43305955u, 0x749f0925u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 136 /* milli weight units */
}
,[TAPLEAF_HASH] =
{ .tag = JET
, .jet = tapleaf_hash
, .cmr = {{0x3539db25u, 0x09aeca7cu, 0xcab8bd45u, 0x24605098u, 0x1aa771b4u, 0x94840bcfu, 0x50ad4465u, 0xda81905au}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 117 /* milli weight units */
}
,[TAPLEAF_VERSION] =
{ .tag = JET
, .jet = tapleaf_version
, .cmr = {{0x7e08fd84u, 0x3cfe1656u, 0x8e176ad4u, 0xbe409ad4u, 0x7b0d4d6bu, 0x56f6a9e4u, 0x852acd87u, 0x2c724206u}}
, .sourceIx = ty_u
, .targetIx = ty_w8
, .cost = 80 /* milli weight units */
}
,[TAPPATH] =
{ .tag = JET
, .jet = tappath
, .cmr = {{0xe2539119u, 0x0bf7a868u, 0xb2eb621bu, 0xc394f6d4u, 0x8a05fbe3u, 0x157529cdu, 0x3cafd517u, 0x1c77e213u}}
, .sourceIx = ty_w8
, .targetIx = ty_mw256
, .cost = 94 /* milli weight units */
}
,[TAPPATH_HASH] =
{ .tag = JET
, .jet = tappath_hash
, .cmr = {{0x2e750995u, 0xe6780661u, 0x321f29f4u, 0x7737f31bu, 0x9fe43d5cu, 0xd4f24a41u, 0x4a5537f7u, 0x37f6fc1du}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 136 /* milli weight units */
}
,[TX_HASH] =
{ .tag = JET
, .jet = tx_hash
, .cmr = {{0x7c3d6776u, 0xd2f61f88u, 0x910f0e3eu, 0xef8aed15u, 0x2ddda127u, 0x8351ba82u, 0xcca589fdu, 0x91fb4993u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 163 /* milli weight units */
}
,[TX_IS_FINAL] =
{ .tag = JET
, .jet = tx_is_final
, .cmr = {{0x391d9ea2u, 0xc9e5f03eu, 0xd7ad7b62u, 0x372a1657u, 0x4c0d336cu, 0x9b65b304u, 0xb8352fe1u, 0x3a011247u}}
, .sourceIx = ty_u
, .targetIx = ty_b
, .cost = 67 /* milli weight units */
}
,[TX_LOCK_DISTANCE] =
{ .tag = JET
, .jet = tx_lock_distance
, .cmr = {{0x3b710877u, 0xf30d97c9u, 0x3b9f3c72u, 0x82c65788u, 0x94c2a2d4u, 0x60848758u, 0x8c742a9cu, 0x4476801eu}}
, .sourceIx = ty_u
, .targetIx = ty_w16
, .cost = 72 /* milli weight units */
}
,[TX_LOCK_DURATION] =
{ .tag = JET
, .jet = tx_lock_duration
, .cmr = {{0x6307dc72u, 0x0d7f1361u, 0xcc5e11dcu, 0x699a665au, 0x184cacceu, 0x834ef14au, 0xb0b5d04eu, 0x58eb0accu}}
, .sourceIx = ty_u
, .targetIx = ty_w16
, .cost = 63 /* milli weight units */
}
,[TX_LOCK_HEIGHT] =
{ .tag = JET
, .jet = tx_lock_height
, .cmr = {{0x4afc960eu, 0xaa9d3202u, 0xecedbdceu, 0xcc831b69u, 0x64c75897u, 0x625d7d5bu, 0x3433c00bu, 0xb7960c9bu}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 71 /* milli weight units */
}
,[TX_LOCK_TIME] =
{ .tag = JET
, .jet = tx_lock_time
, .cmr = {{0x95cf84f8u, 0x8bb55e9au, 0xd1d7bb53u, 0xc0890145u, 0x432e9f45u, 0x24776535u, 0xfbde9474u, 0x680df319u}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 61 /* milli weight units */
}
,[VERIFY] =
{ .tag = JET
, .jet = verify
, .cmr = {{0xa20623b6u, 0x86a6bdb6u, 0x18b50b4cu, 0x5e8eee06u, 0x01cc8401u, 0x34cb9e54u, 0x80f7b6deu, 0x8949489eu}}
, .sourceIx = ty_b
, .targetIx = ty_u
, .cost = 45 /* milli weight units */
}
,[VERSION] =
{ .tag = JET
, .jet = version
, .cmr = {{0xaeb66197u, 0x9afa8777u, 0xf60b141eu, 0x1705d5a9u, 0xc98f9dccu, 0x9bc09505u, 0x4ceec062u, 0xc9ddcfb3u}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 176 /* milli weight units */
}
,[XOR_16] =
{ .tag = JET
, .jet = xor_16
, .cmr = {{0xed598ae3u, 0x6d7561e7u, 0xaa6edc8cu, 0x88a2c886u, 0x66d63fafu, 0x1db322deu, 0x2ac63247u, 0x0d41f1fau}}
, .sourceIx = ty_w32
, .targetIx = ty_w16
, .cost = 133 /* milli weight units */
}
,[XOR_32] =
{ .tag = JET
, .jet = xor_32
, .cmr = {{0x0f1ea1edu, 0x1ff22893u, 0x8b663855u, 0xd150c28eu, 0x7dfa0c17u, 0x84161834u, 0x30683fcau, 0x1e99b5b4u}}
, .sourceIx = ty_w64
, .targetIx = ty_w32
, .cost = 133 /* milli weight units */
}
,[XOR_64] =
{ .tag = JET
, .jet = xor_64
, .cmr = {{0x7d97328du, 0xb212f1aau, 0x00d61562u, 0x075e02c0u, 0xfe49363au, 0x320bf207u, 0x4b7bc300u, 0xe23ab2edu}}
, .sourceIx = ty_w128
, .targetIx = ty_w64
, .cost = 133 /* milli weight units */
}
,[XOR_8] =
{ .tag = JET
, .jet = xor_8
, .cmr = {{0x876cd580u, 0x986bc208u, 0x5ac4f4ebu, 0x5e021e05u, 0x63502d1cu, 0x970870f0u, 0x3e8003b0u, 0x4fe6cf7du}}
, .sourceIx = ty_w16
, .targetIx = ty_w8
, .cost = 133 /* milli weight units */
}
,[XOR_XOR_16] =
{ .tag = JET
, .jet = xor_xor_16
, .cmr = {{0x25dec02cu, 0x5caaeda6u, 0x6ea2ab32u, 0xe5ea41b7u, 0x68241221u, 0x20a3ca0du, 0x9a4ed50eu, 0x8c31c245u}}
, .sourceIx = ty_pw16w32
, .targetIx = ty_w16
, .cost = 133 /* milli weight units */
}
,[XOR_XOR_32] =
{ .tag = JET
, .jet = xor_xor_32
, .cmr = {{0x1e0076a0u, 0x999328aau, 0xce84c482u, 0x780ae586u, 0x937d3e36u, 0x5a3b32eeu, 0x73e2bf04u, 0xc82537d2u}}
, .sourceIx = ty_pw32w64
, .targetIx = ty_w32
, .cost = 133 /* milli weight units */
}
,[XOR_XOR_64] =
{ .tag = JET
, .jet = xor_xor_64
, .cmr = {{0x2b14c327u, 0xc5d53cd1u, 0x25e7429fu, 0x2b97664au, 0x85778cdfu, 0xad2453ecu, 0xb193b35du, 0x8d31ac47u}}
, .sourceIx = ty_pw64w128
, .targetIx = ty_w64
, .cost = 133 /* milli weight units */
}
,[XOR_XOR_8] =
{ .tag = JET
, .jet = xor_xor_8
, .cmr = {{0xe257cb12u, 0xa9632488u, 0xa15d4984u, 0xfa388890u, 0x3a959386u, 0xe84f1c07u, 0xe9d29df7u, 0x12047071u}}
, .sourceIx = ty_pw8w16
, .targetIx = ty_w8
, .cost = 133 /* milli weight units */
}
