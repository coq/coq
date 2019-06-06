(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Coq.Arith.EqNat.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.
Require Export Coq.Init.Byte.

Local Set Implicit Arguments.

Definition eqb (a b : byte) : bool
  := let '(a0, (a1, (a2, (a3, (a4, (a5, (a6, a7))))))) := to_bits a in
     let '(b0, (b1, (b2, (b3, (b4, (b5, (b6, b7))))))) := to_bits b in
     (Bool.eqb a0 b0 && Bool.eqb a1 b1 && Bool.eqb a2 b2 && Bool.eqb a3 b3 &&
          Bool.eqb a4 b4 && Bool.eqb a5 b5 && Bool.eqb a6 b6 && Bool.eqb a7 b7)%bool.

Module Export ByteNotations.
  Export ByteSyntaxNotations.
  Infix "=?" := eqb (at level 70) : byte_scope.
End ByteNotations.

Lemma byte_dec_lb x y : x = y -> eqb x y = true.
Proof. intro; subst y; destruct x; reflexivity. Defined.

Lemma byte_dec_bl x y (H : eqb x y = true) : x = y.
Proof.
  rewrite <- (of_bits_to_bits x), <- (of_bits_to_bits y).
  cbv [eqb] in H; revert H.
  generalize (to_bits x) (to_bits y); clear x y; intros x y H.
  repeat match goal with
         | [ H : and _ _ |- _ ] => destruct H
         | [ H : prod _ _ |- _ ] => destruct H
         | [ H : context[andb _ _ = true] |- _ ] => rewrite Bool.andb_true_iff in H
         | [ H : context[Bool.eqb _ _ = true] |- _ ] => rewrite Bool.eqb_true_iff in H
         | _ => progress subst
         | _ => reflexivity
         end.
Qed.

Lemma eqb_false x y : eqb x y = false -> x <> y.
Proof. intros H H'; pose proof (byte_dec_lb H'); congruence. Qed.

Definition byte_eq_dec (x y : byte) : {x = y} + {x <> y}
  := (if eqb x y as beq return eqb x y = beq -> _
      then fun pf => left (byte_dec_bl x y pf)
      else fun pf => right (eqb_false pf))
       eq_refl.

Section nat.
  Definition to_nat (x : byte) : nat
    := match x with
       | x00 => 0
       | x01 => 1
       | x02 => 2
       | x03 => 3
       | x04 => 4
       | x05 => 5
       | x06 => 6
       | x07 => 7
       | x08 => 8
       | x09 => 9
       | x0a => 10
       | x0b => 11
       | x0c => 12
       | x0d => 13
       | x0e => 14
       | x0f => 15
       | x10 => 16
       | x11 => 17
       | x12 => 18
       | x13 => 19
       | x14 => 20
       | x15 => 21
       | x16 => 22
       | x17 => 23
       | x18 => 24
       | x19 => 25
       | x1a => 26
       | x1b => 27
       | x1c => 28
       | x1d => 29
       | x1e => 30
       | x1f => 31
       | x20 => 32
       | x21 => 33
       | x22 => 34
       | x23 => 35
       | x24 => 36
       | x25 => 37
       | x26 => 38
       | x27 => 39
       | x28 => 40
       | x29 => 41
       | x2a => 42
       | x2b => 43
       | x2c => 44
       | x2d => 45
       | x2e => 46
       | x2f => 47
       | x30 => 48
       | x31 => 49
       | x32 => 50
       | x33 => 51
       | x34 => 52
       | x35 => 53
       | x36 => 54
       | x37 => 55
       | x38 => 56
       | x39 => 57
       | x3a => 58
       | x3b => 59
       | x3c => 60
       | x3d => 61
       | x3e => 62
       | x3f => 63
       | x40 => 64
       | x41 => 65
       | x42 => 66
       | x43 => 67
       | x44 => 68
       | x45 => 69
       | x46 => 70
       | x47 => 71
       | x48 => 72
       | x49 => 73
       | x4a => 74
       | x4b => 75
       | x4c => 76
       | x4d => 77
       | x4e => 78
       | x4f => 79
       | x50 => 80
       | x51 => 81
       | x52 => 82
       | x53 => 83
       | x54 => 84
       | x55 => 85
       | x56 => 86
       | x57 => 87
       | x58 => 88
       | x59 => 89
       | x5a => 90
       | x5b => 91
       | x5c => 92
       | x5d => 93
       | x5e => 94
       | x5f => 95
       | x60 => 96
       | x61 => 97
       | x62 => 98
       | x63 => 99
       | x64 => 100
       | x65 => 101
       | x66 => 102
       | x67 => 103
       | x68 => 104
       | x69 => 105
       | x6a => 106
       | x6b => 107
       | x6c => 108
       | x6d => 109
       | x6e => 110
       | x6f => 111
       | x70 => 112
       | x71 => 113
       | x72 => 114
       | x73 => 115
       | x74 => 116
       | x75 => 117
       | x76 => 118
       | x77 => 119
       | x78 => 120
       | x79 => 121
       | x7a => 122
       | x7b => 123
       | x7c => 124
       | x7d => 125
       | x7e => 126
       | x7f => 127
       | x80 => 128
       | x81 => 129
       | x82 => 130
       | x83 => 131
       | x84 => 132
       | x85 => 133
       | x86 => 134
       | x87 => 135
       | x88 => 136
       | x89 => 137
       | x8a => 138
       | x8b => 139
       | x8c => 140
       | x8d => 141
       | x8e => 142
       | x8f => 143
       | x90 => 144
       | x91 => 145
       | x92 => 146
       | x93 => 147
       | x94 => 148
       | x95 => 149
       | x96 => 150
       | x97 => 151
       | x98 => 152
       | x99 => 153
       | x9a => 154
       | x9b => 155
       | x9c => 156
       | x9d => 157
       | x9e => 158
       | x9f => 159
       | xa0 => 160
       | xa1 => 161
       | xa2 => 162
       | xa3 => 163
       | xa4 => 164
       | xa5 => 165
       | xa6 => 166
       | xa7 => 167
       | xa8 => 168
       | xa9 => 169
       | xaa => 170
       | xab => 171
       | xac => 172
       | xad => 173
       | xae => 174
       | xaf => 175
       | xb0 => 176
       | xb1 => 177
       | xb2 => 178
       | xb3 => 179
       | xb4 => 180
       | xb5 => 181
       | xb6 => 182
       | xb7 => 183
       | xb8 => 184
       | xb9 => 185
       | xba => 186
       | xbb => 187
       | xbc => 188
       | xbd => 189
       | xbe => 190
       | xbf => 191
       | xc0 => 192
       | xc1 => 193
       | xc2 => 194
       | xc3 => 195
       | xc4 => 196
       | xc5 => 197
       | xc6 => 198
       | xc7 => 199
       | xc8 => 200
       | xc9 => 201
       | xca => 202
       | xcb => 203
       | xcc => 204
       | xcd => 205
       | xce => 206
       | xcf => 207
       | xd0 => 208
       | xd1 => 209
       | xd2 => 210
       | xd3 => 211
       | xd4 => 212
       | xd5 => 213
       | xd6 => 214
       | xd7 => 215
       | xd8 => 216
       | xd9 => 217
       | xda => 218
       | xdb => 219
       | xdc => 220
       | xdd => 221
       | xde => 222
       | xdf => 223
       | xe0 => 224
       | xe1 => 225
       | xe2 => 226
       | xe3 => 227
       | xe4 => 228
       | xe5 => 229
       | xe6 => 230
       | xe7 => 231
       | xe8 => 232
       | xe9 => 233
       | xea => 234
       | xeb => 235
       | xec => 236
       | xed => 237
       | xee => 238
       | xef => 239
       | xf0 => 240
       | xf1 => 241
       | xf2 => 242
       | xf3 => 243
       | xf4 => 244
       | xf5 => 245
       | xf6 => 246
       | xf7 => 247
       | xf8 => 248
       | xf9 => 249
       | xfa => 250
       | xfb => 251
       | xfc => 252
       | xfd => 253
       | xfe => 254
       | xff => 255
       end.

  Definition of_nat (x : nat) : option byte
    := match x with
       | 0 => Some x00
       | 1 => Some x01
       | 2 => Some x02
       | 3 => Some x03
       | 4 => Some x04
       | 5 => Some x05
       | 6 => Some x06
       | 7 => Some x07
       | 8 => Some x08
       | 9 => Some x09
       | 10 => Some x0a
       | 11 => Some x0b
       | 12 => Some x0c
       | 13 => Some x0d
       | 14 => Some x0e
       | 15 => Some x0f
       | 16 => Some x10
       | 17 => Some x11
       | 18 => Some x12
       | 19 => Some x13
       | 20 => Some x14
       | 21 => Some x15
       | 22 => Some x16
       | 23 => Some x17
       | 24 => Some x18
       | 25 => Some x19
       | 26 => Some x1a
       | 27 => Some x1b
       | 28 => Some x1c
       | 29 => Some x1d
       | 30 => Some x1e
       | 31 => Some x1f
       | 32 => Some x20
       | 33 => Some x21
       | 34 => Some x22
       | 35 => Some x23
       | 36 => Some x24
       | 37 => Some x25
       | 38 => Some x26
       | 39 => Some x27
       | 40 => Some x28
       | 41 => Some x29
       | 42 => Some x2a
       | 43 => Some x2b
       | 44 => Some x2c
       | 45 => Some x2d
       | 46 => Some x2e
       | 47 => Some x2f
       | 48 => Some x30
       | 49 => Some x31
       | 50 => Some x32
       | 51 => Some x33
       | 52 => Some x34
       | 53 => Some x35
       | 54 => Some x36
       | 55 => Some x37
       | 56 => Some x38
       | 57 => Some x39
       | 58 => Some x3a
       | 59 => Some x3b
       | 60 => Some x3c
       | 61 => Some x3d
       | 62 => Some x3e
       | 63 => Some x3f
       | 64 => Some x40
       | 65 => Some x41
       | 66 => Some x42
       | 67 => Some x43
       | 68 => Some x44
       | 69 => Some x45
       | 70 => Some x46
       | 71 => Some x47
       | 72 => Some x48
       | 73 => Some x49
       | 74 => Some x4a
       | 75 => Some x4b
       | 76 => Some x4c
       | 77 => Some x4d
       | 78 => Some x4e
       | 79 => Some x4f
       | 80 => Some x50
       | 81 => Some x51
       | 82 => Some x52
       | 83 => Some x53
       | 84 => Some x54
       | 85 => Some x55
       | 86 => Some x56
       | 87 => Some x57
       | 88 => Some x58
       | 89 => Some x59
       | 90 => Some x5a
       | 91 => Some x5b
       | 92 => Some x5c
       | 93 => Some x5d
       | 94 => Some x5e
       | 95 => Some x5f
       | 96 => Some x60
       | 97 => Some x61
       | 98 => Some x62
       | 99 => Some x63
       | 100 => Some x64
       | 101 => Some x65
       | 102 => Some x66
       | 103 => Some x67
       | 104 => Some x68
       | 105 => Some x69
       | 106 => Some x6a
       | 107 => Some x6b
       | 108 => Some x6c
       | 109 => Some x6d
       | 110 => Some x6e
       | 111 => Some x6f
       | 112 => Some x70
       | 113 => Some x71
       | 114 => Some x72
       | 115 => Some x73
       | 116 => Some x74
       | 117 => Some x75
       | 118 => Some x76
       | 119 => Some x77
       | 120 => Some x78
       | 121 => Some x79
       | 122 => Some x7a
       | 123 => Some x7b
       | 124 => Some x7c
       | 125 => Some x7d
       | 126 => Some x7e
       | 127 => Some x7f
       | 128 => Some x80
       | 129 => Some x81
       | 130 => Some x82
       | 131 => Some x83
       | 132 => Some x84
       | 133 => Some x85
       | 134 => Some x86
       | 135 => Some x87
       | 136 => Some x88
       | 137 => Some x89
       | 138 => Some x8a
       | 139 => Some x8b
       | 140 => Some x8c
       | 141 => Some x8d
       | 142 => Some x8e
       | 143 => Some x8f
       | 144 => Some x90
       | 145 => Some x91
       | 146 => Some x92
       | 147 => Some x93
       | 148 => Some x94
       | 149 => Some x95
       | 150 => Some x96
       | 151 => Some x97
       | 152 => Some x98
       | 153 => Some x99
       | 154 => Some x9a
       | 155 => Some x9b
       | 156 => Some x9c
       | 157 => Some x9d
       | 158 => Some x9e
       | 159 => Some x9f
       | 160 => Some xa0
       | 161 => Some xa1
       | 162 => Some xa2
       | 163 => Some xa3
       | 164 => Some xa4
       | 165 => Some xa5
       | 166 => Some xa6
       | 167 => Some xa7
       | 168 => Some xa8
       | 169 => Some xa9
       | 170 => Some xaa
       | 171 => Some xab
       | 172 => Some xac
       | 173 => Some xad
       | 174 => Some xae
       | 175 => Some xaf
       | 176 => Some xb0
       | 177 => Some xb1
       | 178 => Some xb2
       | 179 => Some xb3
       | 180 => Some xb4
       | 181 => Some xb5
       | 182 => Some xb6
       | 183 => Some xb7
       | 184 => Some xb8
       | 185 => Some xb9
       | 186 => Some xba
       | 187 => Some xbb
       | 188 => Some xbc
       | 189 => Some xbd
       | 190 => Some xbe
       | 191 => Some xbf
       | 192 => Some xc0
       | 193 => Some xc1
       | 194 => Some xc2
       | 195 => Some xc3
       | 196 => Some xc4
       | 197 => Some xc5
       | 198 => Some xc6
       | 199 => Some xc7
       | 200 => Some xc8
       | 201 => Some xc9
       | 202 => Some xca
       | 203 => Some xcb
       | 204 => Some xcc
       | 205 => Some xcd
       | 206 => Some xce
       | 207 => Some xcf
       | 208 => Some xd0
       | 209 => Some xd1
       | 210 => Some xd2
       | 211 => Some xd3
       | 212 => Some xd4
       | 213 => Some xd5
       | 214 => Some xd6
       | 215 => Some xd7
       | 216 => Some xd8
       | 217 => Some xd9
       | 218 => Some xda
       | 219 => Some xdb
       | 220 => Some xdc
       | 221 => Some xdd
       | 222 => Some xde
       | 223 => Some xdf
       | 224 => Some xe0
       | 225 => Some xe1
       | 226 => Some xe2
       | 227 => Some xe3
       | 228 => Some xe4
       | 229 => Some xe5
       | 230 => Some xe6
       | 231 => Some xe7
       | 232 => Some xe8
       | 233 => Some xe9
       | 234 => Some xea
       | 235 => Some xeb
       | 236 => Some xec
       | 237 => Some xed
       | 238 => Some xee
       | 239 => Some xef
       | 240 => Some xf0
       | 241 => Some xf1
       | 242 => Some xf2
       | 243 => Some xf3
       | 244 => Some xf4
       | 245 => Some xf5
       | 246 => Some xf6
       | 247 => Some xf7
       | 248 => Some xf8
       | 249 => Some xf9
       | 250 => Some xfa
       | 251 => Some xfb
       | 252 => Some xfc
       | 253 => Some xfd
       | 254 => Some xfe
       | 255 => Some xff
       | _ => None
       end.

  Lemma of_to_nat x : of_nat (to_nat x) = Some x.
  Proof. destruct x; reflexivity. Qed.

  Lemma to_of_nat x y : of_nat x = Some y -> to_nat y = x.
  Proof.
    do 256 try destruct x as [|x]; cbv [of_nat]; intro.
    all: repeat match goal with
                | _ => reflexivity
                | _ => progress subst
                | [ H : Some ?a = Some ?b |- _ ] => assert (a = b) by refine match H with eq_refl => eq_refl end; clear H
                | [ H : None = Some _ |- _ ] => solve [ inversion H ]
                end.
  Qed.

  Lemma to_of_nat_iff x y : of_nat x = Some y <-> to_nat y = x.
  Proof. split; intro; subst; (apply of_to_nat || apply to_of_nat); assumption. Qed.

  Lemma to_of_nat_option_map x : option_map to_nat (of_nat x) = if Nat.leb x 255 then Some x else None.
  Proof. do 256 try destruct x as [|x]; reflexivity. Qed.

  Lemma to_nat_bounded x : to_nat x <= 255.
  Proof.
    generalize (to_of_nat_option_map (to_nat x)).
    rewrite of_to_nat; cbn [option_map].
    destruct (Nat.leb (to_nat x) 255) eqn:H; [ | congruence ].
    rewrite (PeanoNat.Nat.leb_le (to_nat x) 255) in H.
    intro; assumption.
  Qed.

  Lemma of_nat_None_iff x : of_nat x = None <-> 255 < x.
  Proof.
    generalize (to_of_nat_option_map x).
    destruct (of_nat x), (Nat.leb x 255) eqn:H; cbn [option_map]; try congruence.
    { rewrite PeanoNat.Nat.leb_le in H; split; [ congruence | ].
      rewrite PeanoNat.Nat.lt_nge; intro H'; exfalso; apply H'; assumption. }
    { rewrite PeanoNat.Nat.leb_nle in H; split; [ | reflexivity ].
      rewrite PeanoNat.Nat.lt_nge; intro; assumption. }
  Qed.
End nat.

Section N.
  Local Open Scope N_scope.

  Definition to_N (x : byte) : N
    := match x with
       | x00 => 0
       | x01 => 1
       | x02 => 2
       | x03 => 3
       | x04 => 4
       | x05 => 5
       | x06 => 6
       | x07 => 7
       | x08 => 8
       | x09 => 9
       | x0a => 10
       | x0b => 11
       | x0c => 12
       | x0d => 13
       | x0e => 14
       | x0f => 15
       | x10 => 16
       | x11 => 17
       | x12 => 18
       | x13 => 19
       | x14 => 20
       | x15 => 21
       | x16 => 22
       | x17 => 23
       | x18 => 24
       | x19 => 25
       | x1a => 26
       | x1b => 27
       | x1c => 28
       | x1d => 29
       | x1e => 30
       | x1f => 31
       | x20 => 32
       | x21 => 33
       | x22 => 34
       | x23 => 35
       | x24 => 36
       | x25 => 37
       | x26 => 38
       | x27 => 39
       | x28 => 40
       | x29 => 41
       | x2a => 42
       | x2b => 43
       | x2c => 44
       | x2d => 45
       | x2e => 46
       | x2f => 47
       | x30 => 48
       | x31 => 49
       | x32 => 50
       | x33 => 51
       | x34 => 52
       | x35 => 53
       | x36 => 54
       | x37 => 55
       | x38 => 56
       | x39 => 57
       | x3a => 58
       | x3b => 59
       | x3c => 60
       | x3d => 61
       | x3e => 62
       | x3f => 63
       | x40 => 64
       | x41 => 65
       | x42 => 66
       | x43 => 67
       | x44 => 68
       | x45 => 69
       | x46 => 70
       | x47 => 71
       | x48 => 72
       | x49 => 73
       | x4a => 74
       | x4b => 75
       | x4c => 76
       | x4d => 77
       | x4e => 78
       | x4f => 79
       | x50 => 80
       | x51 => 81
       | x52 => 82
       | x53 => 83
       | x54 => 84
       | x55 => 85
       | x56 => 86
       | x57 => 87
       | x58 => 88
       | x59 => 89
       | x5a => 90
       | x5b => 91
       | x5c => 92
       | x5d => 93
       | x5e => 94
       | x5f => 95
       | x60 => 96
       | x61 => 97
       | x62 => 98
       | x63 => 99
       | x64 => 100
       | x65 => 101
       | x66 => 102
       | x67 => 103
       | x68 => 104
       | x69 => 105
       | x6a => 106
       | x6b => 107
       | x6c => 108
       | x6d => 109
       | x6e => 110
       | x6f => 111
       | x70 => 112
       | x71 => 113
       | x72 => 114
       | x73 => 115
       | x74 => 116
       | x75 => 117
       | x76 => 118
       | x77 => 119
       | x78 => 120
       | x79 => 121
       | x7a => 122
       | x7b => 123
       | x7c => 124
       | x7d => 125
       | x7e => 126
       | x7f => 127
       | x80 => 128
       | x81 => 129
       | x82 => 130
       | x83 => 131
       | x84 => 132
       | x85 => 133
       | x86 => 134
       | x87 => 135
       | x88 => 136
       | x89 => 137
       | x8a => 138
       | x8b => 139
       | x8c => 140
       | x8d => 141
       | x8e => 142
       | x8f => 143
       | x90 => 144
       | x91 => 145
       | x92 => 146
       | x93 => 147
       | x94 => 148
       | x95 => 149
       | x96 => 150
       | x97 => 151
       | x98 => 152
       | x99 => 153
       | x9a => 154
       | x9b => 155
       | x9c => 156
       | x9d => 157
       | x9e => 158
       | x9f => 159
       | xa0 => 160
       | xa1 => 161
       | xa2 => 162
       | xa3 => 163
       | xa4 => 164
       | xa5 => 165
       | xa6 => 166
       | xa7 => 167
       | xa8 => 168
       | xa9 => 169
       | xaa => 170
       | xab => 171
       | xac => 172
       | xad => 173
       | xae => 174
       | xaf => 175
       | xb0 => 176
       | xb1 => 177
       | xb2 => 178
       | xb3 => 179
       | xb4 => 180
       | xb5 => 181
       | xb6 => 182
       | xb7 => 183
       | xb8 => 184
       | xb9 => 185
       | xba => 186
       | xbb => 187
       | xbc => 188
       | xbd => 189
       | xbe => 190
       | xbf => 191
       | xc0 => 192
       | xc1 => 193
       | xc2 => 194
       | xc3 => 195
       | xc4 => 196
       | xc5 => 197
       | xc6 => 198
       | xc7 => 199
       | xc8 => 200
       | xc9 => 201
       | xca => 202
       | xcb => 203
       | xcc => 204
       | xcd => 205
       | xce => 206
       | xcf => 207
       | xd0 => 208
       | xd1 => 209
       | xd2 => 210
       | xd3 => 211
       | xd4 => 212
       | xd5 => 213
       | xd6 => 214
       | xd7 => 215
       | xd8 => 216
       | xd9 => 217
       | xda => 218
       | xdb => 219
       | xdc => 220
       | xdd => 221
       | xde => 222
       | xdf => 223
       | xe0 => 224
       | xe1 => 225
       | xe2 => 226
       | xe3 => 227
       | xe4 => 228
       | xe5 => 229
       | xe6 => 230
       | xe7 => 231
       | xe8 => 232
       | xe9 => 233
       | xea => 234
       | xeb => 235
       | xec => 236
       | xed => 237
       | xee => 238
       | xef => 239
       | xf0 => 240
       | xf1 => 241
       | xf2 => 242
       | xf3 => 243
       | xf4 => 244
       | xf5 => 245
       | xf6 => 246
       | xf7 => 247
       | xf8 => 248
       | xf9 => 249
       | xfa => 250
       | xfb => 251
       | xfc => 252
       | xfd => 253
       | xfe => 254
       | xff => 255
       end.

  Definition of_N (x : N) : option byte
    := match x with
       | 0 => Some x00
       | 1 => Some x01
       | 2 => Some x02
       | 3 => Some x03
       | 4 => Some x04
       | 5 => Some x05
       | 6 => Some x06
       | 7 => Some x07
       | 8 => Some x08
       | 9 => Some x09
       | 10 => Some x0a
       | 11 => Some x0b
       | 12 => Some x0c
       | 13 => Some x0d
       | 14 => Some x0e
       | 15 => Some x0f
       | 16 => Some x10
       | 17 => Some x11
       | 18 => Some x12
       | 19 => Some x13
       | 20 => Some x14
       | 21 => Some x15
       | 22 => Some x16
       | 23 => Some x17
       | 24 => Some x18
       | 25 => Some x19
       | 26 => Some x1a
       | 27 => Some x1b
       | 28 => Some x1c
       | 29 => Some x1d
       | 30 => Some x1e
       | 31 => Some x1f
       | 32 => Some x20
       | 33 => Some x21
       | 34 => Some x22
       | 35 => Some x23
       | 36 => Some x24
       | 37 => Some x25
       | 38 => Some x26
       | 39 => Some x27
       | 40 => Some x28
       | 41 => Some x29
       | 42 => Some x2a
       | 43 => Some x2b
       | 44 => Some x2c
       | 45 => Some x2d
       | 46 => Some x2e
       | 47 => Some x2f
       | 48 => Some x30
       | 49 => Some x31
       | 50 => Some x32
       | 51 => Some x33
       | 52 => Some x34
       | 53 => Some x35
       | 54 => Some x36
       | 55 => Some x37
       | 56 => Some x38
       | 57 => Some x39
       | 58 => Some x3a
       | 59 => Some x3b
       | 60 => Some x3c
       | 61 => Some x3d
       | 62 => Some x3e
       | 63 => Some x3f
       | 64 => Some x40
       | 65 => Some x41
       | 66 => Some x42
       | 67 => Some x43
       | 68 => Some x44
       | 69 => Some x45
       | 70 => Some x46
       | 71 => Some x47
       | 72 => Some x48
       | 73 => Some x49
       | 74 => Some x4a
       | 75 => Some x4b
       | 76 => Some x4c
       | 77 => Some x4d
       | 78 => Some x4e
       | 79 => Some x4f
       | 80 => Some x50
       | 81 => Some x51
       | 82 => Some x52
       | 83 => Some x53
       | 84 => Some x54
       | 85 => Some x55
       | 86 => Some x56
       | 87 => Some x57
       | 88 => Some x58
       | 89 => Some x59
       | 90 => Some x5a
       | 91 => Some x5b
       | 92 => Some x5c
       | 93 => Some x5d
       | 94 => Some x5e
       | 95 => Some x5f
       | 96 => Some x60
       | 97 => Some x61
       | 98 => Some x62
       | 99 => Some x63
       | 100 => Some x64
       | 101 => Some x65
       | 102 => Some x66
       | 103 => Some x67
       | 104 => Some x68
       | 105 => Some x69
       | 106 => Some x6a
       | 107 => Some x6b
       | 108 => Some x6c
       | 109 => Some x6d
       | 110 => Some x6e
       | 111 => Some x6f
       | 112 => Some x70
       | 113 => Some x71
       | 114 => Some x72
       | 115 => Some x73
       | 116 => Some x74
       | 117 => Some x75
       | 118 => Some x76
       | 119 => Some x77
       | 120 => Some x78
       | 121 => Some x79
       | 122 => Some x7a
       | 123 => Some x7b
       | 124 => Some x7c
       | 125 => Some x7d
       | 126 => Some x7e
       | 127 => Some x7f
       | 128 => Some x80
       | 129 => Some x81
       | 130 => Some x82
       | 131 => Some x83
       | 132 => Some x84
       | 133 => Some x85
       | 134 => Some x86
       | 135 => Some x87
       | 136 => Some x88
       | 137 => Some x89
       | 138 => Some x8a
       | 139 => Some x8b
       | 140 => Some x8c
       | 141 => Some x8d
       | 142 => Some x8e
       | 143 => Some x8f
       | 144 => Some x90
       | 145 => Some x91
       | 146 => Some x92
       | 147 => Some x93
       | 148 => Some x94
       | 149 => Some x95
       | 150 => Some x96
       | 151 => Some x97
       | 152 => Some x98
       | 153 => Some x99
       | 154 => Some x9a
       | 155 => Some x9b
       | 156 => Some x9c
       | 157 => Some x9d
       | 158 => Some x9e
       | 159 => Some x9f
       | 160 => Some xa0
       | 161 => Some xa1
       | 162 => Some xa2
       | 163 => Some xa3
       | 164 => Some xa4
       | 165 => Some xa5
       | 166 => Some xa6
       | 167 => Some xa7
       | 168 => Some xa8
       | 169 => Some xa9
       | 170 => Some xaa
       | 171 => Some xab
       | 172 => Some xac
       | 173 => Some xad
       | 174 => Some xae
       | 175 => Some xaf
       | 176 => Some xb0
       | 177 => Some xb1
       | 178 => Some xb2
       | 179 => Some xb3
       | 180 => Some xb4
       | 181 => Some xb5
       | 182 => Some xb6
       | 183 => Some xb7
       | 184 => Some xb8
       | 185 => Some xb9
       | 186 => Some xba
       | 187 => Some xbb
       | 188 => Some xbc
       | 189 => Some xbd
       | 190 => Some xbe
       | 191 => Some xbf
       | 192 => Some xc0
       | 193 => Some xc1
       | 194 => Some xc2
       | 195 => Some xc3
       | 196 => Some xc4
       | 197 => Some xc5
       | 198 => Some xc6
       | 199 => Some xc7
       | 200 => Some xc8
       | 201 => Some xc9
       | 202 => Some xca
       | 203 => Some xcb
       | 204 => Some xcc
       | 205 => Some xcd
       | 206 => Some xce
       | 207 => Some xcf
       | 208 => Some xd0
       | 209 => Some xd1
       | 210 => Some xd2
       | 211 => Some xd3
       | 212 => Some xd4
       | 213 => Some xd5
       | 214 => Some xd6
       | 215 => Some xd7
       | 216 => Some xd8
       | 217 => Some xd9
       | 218 => Some xda
       | 219 => Some xdb
       | 220 => Some xdc
       | 221 => Some xdd
       | 222 => Some xde
       | 223 => Some xdf
       | 224 => Some xe0
       | 225 => Some xe1
       | 226 => Some xe2
       | 227 => Some xe3
       | 228 => Some xe4
       | 229 => Some xe5
       | 230 => Some xe6
       | 231 => Some xe7
       | 232 => Some xe8
       | 233 => Some xe9
       | 234 => Some xea
       | 235 => Some xeb
       | 236 => Some xec
       | 237 => Some xed
       | 238 => Some xee
       | 239 => Some xef
       | 240 => Some xf0
       | 241 => Some xf1
       | 242 => Some xf2
       | 243 => Some xf3
       | 244 => Some xf4
       | 245 => Some xf5
       | 246 => Some xf6
       | 247 => Some xf7
       | 248 => Some xf8
       | 249 => Some xf9
       | 250 => Some xfa
       | 251 => Some xfb
       | 252 => Some xfc
       | 253 => Some xfd
       | 254 => Some xfe
       | 255 => Some xff
       | _ => None
       end.

  Lemma of_to_N x : of_N (to_N x) = Some x.
  Proof. destruct x; reflexivity. Qed.

  Lemma to_of_N x y : of_N x = Some y -> to_N y = x.
  Proof.
    cbv [of_N];
      repeat match goal with
             | [ |- context[match ?x with _ => _ end] ] => is_var x; destruct x
             | _ => intro
             | _ => reflexivity
             | _ => progress subst
             | [ H : Some ?a = Some ?b |- _ ] => assert (a = b) by refine match H with eq_refl => eq_refl end; clear H
             | [ H : None = Some _ |- _ ] => solve [ inversion H ]
             end.
  Qed.

  Lemma to_of_N_iff x y : of_N x = Some y <-> to_N y = x.
  Proof. split; intro; subst; (apply of_to_N || apply to_of_N); assumption. Qed.

  Lemma to_of_N_option_map x : option_map to_N (of_N x) = if N.leb x 255 then Some x else None.
  Proof.
    cbv [of_N];
      repeat match goal with
             | [ |- context[match ?x with _ => _ end] ] => is_var x; destruct x
             end;
      reflexivity.
  Qed.

  Lemma to_N_bounded x : to_N x <= 255.
  Proof.
    generalize (to_of_N_option_map (to_N x)).
    rewrite of_to_N; cbn [option_map].
    destruct (N.leb (to_N x) 255) eqn:H; [ | congruence ].
    rewrite (N.leb_le (to_N x) 255) in H.
    intro; assumption.
  Qed.

  Lemma of_N_None_iff x : of_N x = None <-> 255 < x.
  Proof.
    generalize (to_of_N_option_map x).
    destruct (of_N x), (N.leb x 255) eqn:H; cbn [option_map]; try congruence.
    { rewrite N.leb_le in H; split; [ congruence | ].
      rewrite N.lt_nge; intro H'; exfalso; apply H'; assumption. }
    { rewrite N.leb_nle in H; split; [ | reflexivity ].
      rewrite N.lt_nge; intro; assumption. }
  Qed.

  Lemma to_N_via_nat x : to_N x = N.of_nat (to_nat x).
  Proof. destruct x; reflexivity. Qed.

  Lemma to_nat_via_N x : to_nat x = N.to_nat (to_N x).
  Proof. destruct x; reflexivity. Qed.

  Lemma of_N_via_nat x : of_N x = of_nat (N.to_nat x).
  Proof.
    destruct (of_N x) as [b|] eqn:H1.
    { rewrite to_of_N_iff in H1; subst.
      destruct b; reflexivity. }
    { rewrite of_N_None_iff, <- N.compare_lt_iff in H1.
      symmetry; rewrite of_nat_None_iff, <- PeanoNat.Nat.compare_lt_iff.
      rewrite Nat2N.inj_compare, N2Nat.id; assumption. }
  Qed.

  Lemma of_nat_via_N x : of_nat x = of_N (N.of_nat x).
  Proof.
    destruct (of_nat x) as [b|] eqn:H1.
    { rewrite to_of_nat_iff in H1; subst.
      destruct b; reflexivity. }
    { rewrite of_nat_None_iff, <- PeanoNat.Nat.compare_lt_iff in H1.
      symmetry; rewrite of_N_None_iff, <- N.compare_lt_iff.
      rewrite N2Nat.inj_compare, Nat2N.id; assumption. }
  Qed.
End N.
