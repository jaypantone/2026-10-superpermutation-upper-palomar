module

public import upper.partition.seed_chunks.Chunk000
public import upper.partition.seed_chunks.Chunk001
public import upper.partition.seed_chunks.Chunk002
public import upper.partition.seed_chunks.Chunk003
public import upper.partition.seed_chunks.Chunk004
public import upper.partition.seed_chunks.Chunk005
public import upper.partition.seed_chunks.Chunk006
public import upper.partition.seed_chunks.Chunk007
public import upper.partition.seed_chunks.Chunk008
public import upper.partition.seed_chunks.Chunk009
public import upper.partition.seed_chunks.Chunk010
public import upper.partition.seed_chunks.Chunk011
public import upper.partition.seed_chunks.Chunk012
public import upper.partition.seed_chunks.Chunk013
public import upper.partition.seed_chunks.Chunk014
public import upper.partition.seed_chunks.Chunk015
public import upper.partition.seed_chunks.Chunk016
public import upper.partition.seed_chunks.Chunk017
public import upper.partition.seed_chunks.Chunk018
public import upper.partition.seed_chunks.Chunk019
public import upper.partition.seed_chunks.Chunk020
public import upper.partition.seed_chunks.Chunk021
public import upper.partition.seed_chunks.Chunk022
public import upper.partition.seed_chunks.Chunk023
public import upper.partition.seed_chunks.Chunk024
public import upper.partition.seed_chunks.Chunk025
public import upper.partition.seed_chunks.Chunk026
public import upper.partition.seed_chunks.Chunk027
public import upper.partition.seed_chunks.Chunk028
public import upper.partition.seed_chunks.Chunk029
public import upper.partition.seed_chunks.Chunk030
public import upper.partition.seed_chunks.Chunk031
public import upper.partition.seed_chunks.Chunk032
public import upper.partition.seed_chunks.Chunk033
public import upper.partition.seed_chunks.Chunk034
public import upper.partition.seed_chunks.Chunk035
public import upper.partition.seed_chunks.Chunk036
public import upper.partition.seed_chunks.Chunk037
public import upper.partition.seed_chunks.Chunk038
public import upper.partition.seed_chunks.Chunk039

@[expose] public section

/-! All seed source rows are covered by consecutive bounded witnesses.
The former whole-inventory sorting equality is retained only as historical source. -/
namespace SuperpermutationUpperBound.Native14.Partition

theorem canonicalSeedRows_length : canonicalSeedRows.length = 5040 := by
  calc
    canonicalSeedRows.length = (List.permutations' [1,2,3,4,5,6,7]).length :=
      List.length_map (fun x : List Nat => Row.mk (0::x) 12 8)
    _ = (List.permutations [1,2,3,4,5,6,7]).length :=
      (List.permutations_perm_permutations' _).length_eq.symm
    _ = 5040 := by rw [List.length_permutations]; decide

theorem canonicalSeedRows_refines : BlockRefines canonicalSeedRows completeSeedRows := by
  have h158 : BlockRefines (canonicalSeedRows.drop 5040) completeSeedRows :=
    blockRefines_drop_end 5040 (by rw [canonicalSeedRows_length])
  have h157 := blockRefines_drop_step 5024 16
    SeedChunks.Chunk039.refines01 h158
  have h156 := blockRefines_drop_step 4992 32
    SeedChunks.Chunk039.refines00 h157
  have h155 := blockRefines_drop_step 4960 32
    SeedChunks.Chunk038.refines03 h156
  have h154 := blockRefines_drop_step 4928 32
    SeedChunks.Chunk038.refines02 h155
  have h153 := blockRefines_drop_step 4896 32
    SeedChunks.Chunk038.refines01 h154
  have h152 := blockRefines_drop_step 4864 32
    SeedChunks.Chunk038.refines00 h153
  have h151 := blockRefines_drop_step 4832 32
    SeedChunks.Chunk037.refines03 h152
  have h150 := blockRefines_drop_step 4800 32
    SeedChunks.Chunk037.refines02 h151
  have h149 := blockRefines_drop_step 4768 32
    SeedChunks.Chunk037.refines01 h150
  have h148 := blockRefines_drop_step 4736 32
    SeedChunks.Chunk037.refines00 h149
  have h147 := blockRefines_drop_step 4704 32
    SeedChunks.Chunk036.refines03 h148
  have h146 := blockRefines_drop_step 4672 32
    SeedChunks.Chunk036.refines02 h147
  have h145 := blockRefines_drop_step 4640 32
    SeedChunks.Chunk036.refines01 h146
  have h144 := blockRefines_drop_step 4608 32
    SeedChunks.Chunk036.refines00 h145
  have h143 := blockRefines_drop_step 4576 32
    SeedChunks.Chunk035.refines03 h144
  have h142 := blockRefines_drop_step 4544 32
    SeedChunks.Chunk035.refines02 h143
  have h141 := blockRefines_drop_step 4512 32
    SeedChunks.Chunk035.refines01 h142
  have h140 := blockRefines_drop_step 4480 32
    SeedChunks.Chunk035.refines00 h141
  have h139 := blockRefines_drop_step 4448 32
    SeedChunks.Chunk034.refines03 h140
  have h138 := blockRefines_drop_step 4416 32
    SeedChunks.Chunk034.refines02 h139
  have h137 := blockRefines_drop_step 4384 32
    SeedChunks.Chunk034.refines01 h138
  have h136 := blockRefines_drop_step 4352 32
    SeedChunks.Chunk034.refines00 h137
  have h135 := blockRefines_drop_step 4320 32
    SeedChunks.Chunk033.refines03 h136
  have h134 := blockRefines_drop_step 4288 32
    SeedChunks.Chunk033.refines02 h135
  have h133 := blockRefines_drop_step 4256 32
    SeedChunks.Chunk033.refines01 h134
  have h132 := blockRefines_drop_step 4224 32
    SeedChunks.Chunk033.refines00 h133
  have h131 := blockRefines_drop_step 4192 32
    SeedChunks.Chunk032.refines03 h132
  have h130 := blockRefines_drop_step 4160 32
    SeedChunks.Chunk032.refines02 h131
  have h129 := blockRefines_drop_step 4128 32
    SeedChunks.Chunk032.refines01 h130
  have h128 := blockRefines_drop_step 4096 32
    SeedChunks.Chunk032.refines00 h129
  have h127 := blockRefines_drop_step 4064 32
    SeedChunks.Chunk031.refines03 h128
  have h126 := blockRefines_drop_step 4032 32
    SeedChunks.Chunk031.refines02 h127
  have h125 := blockRefines_drop_step 4000 32
    SeedChunks.Chunk031.refines01 h126
  have h124 := blockRefines_drop_step 3968 32
    SeedChunks.Chunk031.refines00 h125
  have h123 := blockRefines_drop_step 3936 32
    SeedChunks.Chunk030.refines03 h124
  have h122 := blockRefines_drop_step 3904 32
    SeedChunks.Chunk030.refines02 h123
  have h121 := blockRefines_drop_step 3872 32
    SeedChunks.Chunk030.refines01 h122
  have h120 := blockRefines_drop_step 3840 32
    SeedChunks.Chunk030.refines00 h121
  have h119 := blockRefines_drop_step 3808 32
    SeedChunks.Chunk029.refines03 h120
  have h118 := blockRefines_drop_step 3776 32
    SeedChunks.Chunk029.refines02 h119
  have h117 := blockRefines_drop_step 3744 32
    SeedChunks.Chunk029.refines01 h118
  have h116 := blockRefines_drop_step 3712 32
    SeedChunks.Chunk029.refines00 h117
  have h115 := blockRefines_drop_step 3680 32
    SeedChunks.Chunk028.refines03 h116
  have h114 := blockRefines_drop_step 3648 32
    SeedChunks.Chunk028.refines02 h115
  have h113 := blockRefines_drop_step 3616 32
    SeedChunks.Chunk028.refines01 h114
  have h112 := blockRefines_drop_step 3584 32
    SeedChunks.Chunk028.refines00 h113
  have h111 := blockRefines_drop_step 3552 32
    SeedChunks.Chunk027.refines03 h112
  have h110 := blockRefines_drop_step 3520 32
    SeedChunks.Chunk027.refines02 h111
  have h109 := blockRefines_drop_step 3488 32
    SeedChunks.Chunk027.refines01 h110
  have h108 := blockRefines_drop_step 3456 32
    SeedChunks.Chunk027.refines00 h109
  have h107 := blockRefines_drop_step 3424 32
    SeedChunks.Chunk026.refines03 h108
  have h106 := blockRefines_drop_step 3392 32
    SeedChunks.Chunk026.refines02 h107
  have h105 := blockRefines_drop_step 3360 32
    SeedChunks.Chunk026.refines01 h106
  have h104 := blockRefines_drop_step 3328 32
    SeedChunks.Chunk026.refines00 h105
  have h103 := blockRefines_drop_step 3296 32
    SeedChunks.Chunk025.refines03 h104
  have h102 := blockRefines_drop_step 3264 32
    SeedChunks.Chunk025.refines02 h103
  have h101 := blockRefines_drop_step 3232 32
    SeedChunks.Chunk025.refines01 h102
  have h100 := blockRefines_drop_step 3200 32
    SeedChunks.Chunk025.refines00 h101
  have h99 := blockRefines_drop_step 3168 32
    SeedChunks.Chunk024.refines03 h100
  have h98 := blockRefines_drop_step 3136 32
    SeedChunks.Chunk024.refines02 h99
  have h97 := blockRefines_drop_step 3104 32
    SeedChunks.Chunk024.refines01 h98
  have h96 := blockRefines_drop_step 3072 32
    SeedChunks.Chunk024.refines00 h97
  have h95 := blockRefines_drop_step 3040 32
    SeedChunks.Chunk023.refines03 h96
  have h94 := blockRefines_drop_step 3008 32
    SeedChunks.Chunk023.refines02 h95
  have h93 := blockRefines_drop_step 2976 32
    SeedChunks.Chunk023.refines01 h94
  have h92 := blockRefines_drop_step 2944 32
    SeedChunks.Chunk023.refines00 h93
  have h91 := blockRefines_drop_step 2912 32
    SeedChunks.Chunk022.refines03 h92
  have h90 := blockRefines_drop_step 2880 32
    SeedChunks.Chunk022.refines02 h91
  have h89 := blockRefines_drop_step 2848 32
    SeedChunks.Chunk022.refines01 h90
  have h88 := blockRefines_drop_step 2816 32
    SeedChunks.Chunk022.refines00 h89
  have h87 := blockRefines_drop_step 2784 32
    SeedChunks.Chunk021.refines03 h88
  have h86 := blockRefines_drop_step 2752 32
    SeedChunks.Chunk021.refines02 h87
  have h85 := blockRefines_drop_step 2720 32
    SeedChunks.Chunk021.refines01 h86
  have h84 := blockRefines_drop_step 2688 32
    SeedChunks.Chunk021.refines00 h85
  have h83 := blockRefines_drop_step 2656 32
    SeedChunks.Chunk020.refines03 h84
  have h82 := blockRefines_drop_step 2624 32
    SeedChunks.Chunk020.refines02 h83
  have h81 := blockRefines_drop_step 2592 32
    SeedChunks.Chunk020.refines01 h82
  have h80 := blockRefines_drop_step 2560 32
    SeedChunks.Chunk020.refines00 h81
  have h79 := blockRefines_drop_step 2528 32
    SeedChunks.Chunk019.refines03 h80
  have h78 := blockRefines_drop_step 2496 32
    SeedChunks.Chunk019.refines02 h79
  have h77 := blockRefines_drop_step 2464 32
    SeedChunks.Chunk019.refines01 h78
  have h76 := blockRefines_drop_step 2432 32
    SeedChunks.Chunk019.refines00 h77
  have h75 := blockRefines_drop_step 2400 32
    SeedChunks.Chunk018.refines03 h76
  have h74 := blockRefines_drop_step 2368 32
    SeedChunks.Chunk018.refines02 h75
  have h73 := blockRefines_drop_step 2336 32
    SeedChunks.Chunk018.refines01 h74
  have h72 := blockRefines_drop_step 2304 32
    SeedChunks.Chunk018.refines00 h73
  have h71 := blockRefines_drop_step 2272 32
    SeedChunks.Chunk017.refines03 h72
  have h70 := blockRefines_drop_step 2240 32
    SeedChunks.Chunk017.refines02 h71
  have h69 := blockRefines_drop_step 2208 32
    SeedChunks.Chunk017.refines01 h70
  have h68 := blockRefines_drop_step 2176 32
    SeedChunks.Chunk017.refines00 h69
  have h67 := blockRefines_drop_step 2144 32
    SeedChunks.Chunk016.refines03 h68
  have h66 := blockRefines_drop_step 2112 32
    SeedChunks.Chunk016.refines02 h67
  have h65 := blockRefines_drop_step 2080 32
    SeedChunks.Chunk016.refines01 h66
  have h64 := blockRefines_drop_step 2048 32
    SeedChunks.Chunk016.refines00 h65
  have h63 := blockRefines_drop_step 2016 32
    SeedChunks.Chunk015.refines03 h64
  have h62 := blockRefines_drop_step 1984 32
    SeedChunks.Chunk015.refines02 h63
  have h61 := blockRefines_drop_step 1952 32
    SeedChunks.Chunk015.refines01 h62
  have h60 := blockRefines_drop_step 1920 32
    SeedChunks.Chunk015.refines00 h61
  have h59 := blockRefines_drop_step 1888 32
    SeedChunks.Chunk014.refines03 h60
  have h58 := blockRefines_drop_step 1856 32
    SeedChunks.Chunk014.refines02 h59
  have h57 := blockRefines_drop_step 1824 32
    SeedChunks.Chunk014.refines01 h58
  have h56 := blockRefines_drop_step 1792 32
    SeedChunks.Chunk014.refines00 h57
  have h55 := blockRefines_drop_step 1760 32
    SeedChunks.Chunk013.refines03 h56
  have h54 := blockRefines_drop_step 1728 32
    SeedChunks.Chunk013.refines02 h55
  have h53 := blockRefines_drop_step 1696 32
    SeedChunks.Chunk013.refines01 h54
  have h52 := blockRefines_drop_step 1664 32
    SeedChunks.Chunk013.refines00 h53
  have h51 := blockRefines_drop_step 1632 32
    SeedChunks.Chunk012.refines03 h52
  have h50 := blockRefines_drop_step 1600 32
    SeedChunks.Chunk012.refines02 h51
  have h49 := blockRefines_drop_step 1568 32
    SeedChunks.Chunk012.refines01 h50
  have h48 := blockRefines_drop_step 1536 32
    SeedChunks.Chunk012.refines00 h49
  have h47 := blockRefines_drop_step 1504 32
    SeedChunks.Chunk011.refines03 h48
  have h46 := blockRefines_drop_step 1472 32
    SeedChunks.Chunk011.refines02 h47
  have h45 := blockRefines_drop_step 1440 32
    SeedChunks.Chunk011.refines01 h46
  have h44 := blockRefines_drop_step 1408 32
    SeedChunks.Chunk011.refines00 h45
  have h43 := blockRefines_drop_step 1376 32
    SeedChunks.Chunk010.refines03 h44
  have h42 := blockRefines_drop_step 1344 32
    SeedChunks.Chunk010.refines02 h43
  have h41 := blockRefines_drop_step 1312 32
    SeedChunks.Chunk010.refines01 h42
  have h40 := blockRefines_drop_step 1280 32
    SeedChunks.Chunk010.refines00 h41
  have h39 := blockRefines_drop_step 1248 32
    SeedChunks.Chunk009.refines03 h40
  have h38 := blockRefines_drop_step 1216 32
    SeedChunks.Chunk009.refines02 h39
  have h37 := blockRefines_drop_step 1184 32
    SeedChunks.Chunk009.refines01 h38
  have h36 := blockRefines_drop_step 1152 32
    SeedChunks.Chunk009.refines00 h37
  have h35 := blockRefines_drop_step 1120 32
    SeedChunks.Chunk008.refines03 h36
  have h34 := blockRefines_drop_step 1088 32
    SeedChunks.Chunk008.refines02 h35
  have h33 := blockRefines_drop_step 1056 32
    SeedChunks.Chunk008.refines01 h34
  have h32 := blockRefines_drop_step 1024 32
    SeedChunks.Chunk008.refines00 h33
  have h31 := blockRefines_drop_step 992 32
    SeedChunks.Chunk007.refines03 h32
  have h30 := blockRefines_drop_step 960 32
    SeedChunks.Chunk007.refines02 h31
  have h29 := blockRefines_drop_step 928 32
    SeedChunks.Chunk007.refines01 h30
  have h28 := blockRefines_drop_step 896 32
    SeedChunks.Chunk007.refines00 h29
  have h27 := blockRefines_drop_step 864 32
    SeedChunks.Chunk006.refines03 h28
  have h26 := blockRefines_drop_step 832 32
    SeedChunks.Chunk006.refines02 h27
  have h25 := blockRefines_drop_step 800 32
    SeedChunks.Chunk006.refines01 h26
  have h24 := blockRefines_drop_step 768 32
    SeedChunks.Chunk006.refines00 h25
  have h23 := blockRefines_drop_step 736 32
    SeedChunks.Chunk005.refines03 h24
  have h22 := blockRefines_drop_step 704 32
    SeedChunks.Chunk005.refines02 h23
  have h21 := blockRefines_drop_step 672 32
    SeedChunks.Chunk005.refines01 h22
  have h20 := blockRefines_drop_step 640 32
    SeedChunks.Chunk005.refines00 h21
  have h19 := blockRefines_drop_step 608 32
    SeedChunks.Chunk004.refines03 h20
  have h18 := blockRefines_drop_step 576 32
    SeedChunks.Chunk004.refines02 h19
  have h17 := blockRefines_drop_step 544 32
    SeedChunks.Chunk004.refines01 h18
  have h16 := blockRefines_drop_step 512 32
    SeedChunks.Chunk004.refines00 h17
  have h15 := blockRefines_drop_step 480 32
    SeedChunks.Chunk003.refines03 h16
  have h14 := blockRefines_drop_step 448 32
    SeedChunks.Chunk003.refines02 h15
  have h13 := blockRefines_drop_step 416 32
    SeedChunks.Chunk003.refines01 h14
  have h12 := blockRefines_drop_step 384 32
    SeedChunks.Chunk003.refines00 h13
  have h11 := blockRefines_drop_step 352 32
    SeedChunks.Chunk002.refines03 h12
  have h10 := blockRefines_drop_step 320 32
    SeedChunks.Chunk002.refines02 h11
  have h9 := blockRefines_drop_step 288 32
    SeedChunks.Chunk002.refines01 h10
  have h8 := blockRefines_drop_step 256 32
    SeedChunks.Chunk002.refines00 h9
  have h7 := blockRefines_drop_step 224 32
    SeedChunks.Chunk001.refines03 h8
  have h6 := blockRefines_drop_step 192 32
    SeedChunks.Chunk001.refines02 h7
  have h5 := blockRefines_drop_step 160 32
    SeedChunks.Chunk001.refines01 h6
  have h4 := blockRefines_drop_step 128 32
    SeedChunks.Chunk001.refines00 h5
  have h3 := blockRefines_drop_step 96 32
    SeedChunks.Chunk000.refines03 h4
  have h2 := blockRefines_drop_step 64 32
    SeedChunks.Chunk000.refines02 h3
  have h1 := blockRefines_drop_step 32 32
    SeedChunks.Chunk000.refines01 h2
  have h0 := blockRefines_drop_step 0 32
    SeedChunks.Chunk000.refines00 h1
  simpa only [List.drop_zero] using h0

theorem completeSeedRows_complete : BlockComplete (List.range 8) completeSeedRows :=
  canonicalSeedRows_refines.complete canonicalSeedRows_complete

end SuperpermutationUpperBound.Native14.Partition
