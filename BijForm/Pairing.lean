import BijForm.Coding

namespace BijForm
namespace Pairing

/-
This module proves a shell-based natural-number pairing function and records a
closed-form optimization target. The closed arithmetic expression is

  (g + s - 2) * 2^s + y * 2^g + x + 2

after measuring `x` and `y` as binary strings. Over `Nat`, the leading integer
offset is negative in the first shells, so the proved definition uses the
equivalent shell start plus within-shell position.
-/

def pow2 (n : Nat) : Nat :=
  2 ^ n

def len (x : Nat) : Nat :=
  Nat.log2 (x + 1)

def blockStart (g : Nat) : Nat :=
  pow2 g - 1

def shellSize (s : Nat) : Nat :=
  (s + 1) * pow2 s

def shellStart : Nat → Nat
  | 0 => 0
  | s + 1 => shellStart s + shellSize s

def shellStartClosed : Nat → Nat
  | 0 => 0
  | s + 1 => s * pow2 (s + 1) + 1

def shellGap : Nat → Nat → Nat
  | _, 0 => 0
  | s, k + 1 => shellSize s + shellGap (s + 1) k

def shellPos (x y : Nat) : Nat :=
  let g := len x
  let h := len y
  let xp := x - blockStart g
  let yp := y - blockStart h
  g * pow2 (g + h) + yp * pow2 g + xp

def encode (x y : Nat) : Nat :=
  let g := len x
  let h := len y
  shellStart (g + h) + shellPos x y

def encodeFast (x y : Nat) : Nat :=
  let g := len x
  let h := len y
  shellStartClosed (g + h) + shellPos x y

def locateShellFromCore : Nat × Nat → Nat × Nat
  | (s, n) =>
      if h : n < shellSize s then
        have _ : n < shellSize s := h
        (s, n)
      else
        locateShellFromCore (s + 1, n - shellSize s)
termination_by sn => sn.2
decreasing_by
  simp_wf
  have hsize : 0 < shellSize s := by
    unfold shellSize pow2
    exact Nat.mul_pos (Nat.succ_pos s) (Nat.two_pow_pos s)
  have hsle : shellSize s ≤ n := Nat.le_of_not_gt h
  exact Nat.sub_lt (Nat.lt_of_lt_of_le hsize hsle) hsize

def locateShellFrom (s n : Nat) : Nat × Nat :=
  locateShellFromCore (s, n)

def locateShell (n : Nat) : Nat × Nat :=
  locateShellFrom 0 n

def decodeInShell (s p : Nat) : Nat × Nat :=
  let g := p / pow2 s
  let q := p % pow2 s
  let x := blockStart g + q % pow2 g
  let y := blockStart (s - g) + q / pow2 g
  (x, y)

def bitLen : Nat → Nat
  | 0 => 0
  | n + 1 => Nat.log2 (n + 1) + 1

def clwCore (n : Nat) : Nat :=
  let r := bitLen n - 1
  let w := r - bitLen r
  if bitLen w + w = r then
    w
  else
    w + 1

def clw (n : Nat) : Nat :=
  let w := clwCore n
  if w * pow2 (w + 1) < n then
    w + 1
  else
    w

def decodeFast (n : Nat) : Nat × Nat :=
  let s := clw n
  decodeInShell s (n - shellStartClosed s)

def decode (n : Nat) : Nat × Nat :=
  let sp := locateShell n
  decodeInShell sp.1 sp.2

theorem pow2_pos (n : Nat) : 0 < pow2 n := by
  unfold pow2
  exact Nat.two_pow_pos n

theorem bitLen_mono {a b : Nat} (h : a ≤ b) : bitLen a ≤ bitLen b := by
  cases a with
  | zero =>
      simp [bitLen]
  | succ a =>
      cases b with
      | zero =>
          omega
      | succ b =>
          unfold bitLen
          apply Nat.succ_le_succ
          have ha : a + 1 ≠ 0 := by omega
          have hb : b + 1 ≠ 0 := by omega
          exact (Nat.le_log2 hb).mpr (Nat.le_trans (Nat.log2_self_le ha) h)

theorem lt_pow2_bitLen (n : Nat) : n < pow2 (bitLen n) := by
  cases n with
  | zero =>
      simp [bitLen, pow2]
  | succ n =>
      unfold bitLen pow2
      exact Nat.lt_log2_self

theorem pow2_bitLen_pred_le {n : Nat} (hn : 0 < n) :
    pow2 (bitLen n - 1) ≤ n := by
  cases n with
  | zero =>
      omega
  | succ n =>
      unfold bitLen pow2
      simpa using Nat.log2_self_le (n := n + 1) (by omega)

theorem bitLen_le_self (n : Nat) : bitLen n ≤ n := by
  cases n with
  | zero =>
      simp [bitLen]
  | succ n =>
      simp [bitLen]
      have h : Nat.log2 (n + 1) < n + 1 := by
        exact (Nat.log2_lt (by omega)).mpr Nat.lt_two_pow_self
      omega

theorem bitLen_le_of_lt_pow2 {n k : Nat} (h : n < pow2 k) :
    bitLen n ≤ k := by
  cases n with
  | zero =>
      simp [bitLen]
  | succ n =>
      unfold bitLen
      apply Nat.succ_le_of_lt
      exact (Nat.log2_lt (by omega)).mpr (by simpa [pow2] using h)

theorem mul_add_mod_of_lt {k m r : Nat} (hr : r < k) :
    (m * k + r) % k = r := by
  calc
    (m * k + r) % k = (r + m * k) % k := by rw [Nat.add_comm]
    _ = (r + k * m) % k := by rw [Nat.mul_comm m k]
    _ = r % k := Nat.add_mul_mod_self_left r k m
    _ = r := Nat.mod_eq_of_lt hr

theorem mul_add_div_of_lt {k m r : Nat} (hk : 0 < k) (hr : r < k) :
    (m * k + r) / k = m := by
  calc
    (m * k + r) / k = (r + m * k) / k := by rw [Nat.add_comm]
    _ = r / k + m := Nat.add_mul_div_right r m hk
    _ = m := by
      rw [Nat.div_eq_of_lt hr]
      exact Nat.zero_add m

theorem block_bounds (x : Nat) :
    blockStart (len x) ≤ x ∧ x < blockStart (len x) + pow2 (len x) := by
  have hxpos : x + 1 ≠ 0 := by omega
  have hupper : x + 1 < pow2 (len x + 1) := by
    unfold len pow2
    exact (Nat.log2_lt hxpos).mp (Nat.lt_add_one (Nat.log2 (x + 1)))
  have hlower : pow2 (len x) ≤ x + 1 := by
    apply Nat.le_of_not_gt
    intro hlt
    have hlog : len x < len x := by
      unfold len pow2 at hlt
      exact (Nat.log2_lt hxpos).mpr hlt
    exact Nat.lt_irrefl (len x) hlog
  have hpow : pow2 (len x + 1) = pow2 (len x) + pow2 (len x) := by
    unfold pow2
    rw [Nat.pow_succ]
    omega
  constructor
  · unfold blockStart
    omega
  · unfold blockStart
    rw [hpow] at hupper
    omega

theorem block_residual_lt (x : Nat) :
    x - blockStart (len x) < pow2 (len x) := by
  exact Nat.sub_lt_left_of_lt_add (block_bounds x).1 (block_bounds x).2

theorem block_recompose (x : Nat) :
    blockStart (len x) + (x - blockStart (len x)) = x := by
  have h := (block_bounds x).1
  exact Nat.add_sub_of_le h

theorem len_block {g r : Nat} (hr : r < pow2 g) :
    len (blockStart g + r) = g := by
  have hpos : 0 < pow2 g := pow2_pos g
  have hsucc : blockStart g + r + 1 = pow2 g + r := by
    unfold blockStart
    omega
  have hxpos : blockStart g + r + 1 ≠ 0 := by omega
  have hupper : blockStart g + r + 1 < pow2 (g + 1) := by
    rw [hsucc]
    have hpow : pow2 (g + 1) = pow2 g + pow2 g := by
      unfold pow2
      rw [Nat.pow_succ]
      omega
    rw [hpow]
    omega
  have hlower : ¬blockStart g + r + 1 < pow2 g := by
    rw [hsucc]
    omega
  have hlt_succ : len (blockStart g + r) < g + 1 := by
    unfold len
    exact (Nat.log2_lt hxpos).mpr hupper
  have hnot_lt : ¬len (blockStart g + r) < g := by
    intro hlt
    have hsmall : blockStart g + r + 1 < pow2 g := by
      unfold len at hlt
      exact (Nat.log2_lt hxpos).mp hlt
    exact hlower hsmall
  exact Nat.eq_of_lt_succ_of_not_lt hlt_succ hnot_lt

theorem div_pow2_lt_pow2_sub {s g q : Nat} (hg : g ≤ s) (hq : q < pow2 s) :
    q / pow2 g < pow2 (s - g) := by
  have hpow : pow2 (s - g) * pow2 g = pow2 s := by
    unfold pow2
    exact Nat.pow_sub_mul_pow 2 hg
  exact (Nat.div_lt_iff_lt_mul (pow2_pos g)).mpr (by simpa [hpow] using hq)

theorem div_pow2_le_shell {s p : Nat} (hp : p < shellSize s) :
    p / pow2 s ≤ s := by
  have hlt : p / pow2 s < s + 1 := by
    exact (Nat.div_lt_iff_lt_mul (pow2_pos s)).mpr (by
      simpa [shellSize] using hp)
  exact Nat.le_of_lt_succ hlt

theorem shellTail_lt (x y : Nat) :
    let g := len x
    let h := len y
    (y - blockStart h) * pow2 g + (x - blockStart g) < pow2 (g + h) := by
  dsimp
  let g := len x
  let h := len y
  let xp := x - blockStart g
  let yp := y - blockStart h
  have hx : xp < pow2 g := by
    simpa [g, xp] using block_residual_lt x
  have hy : yp < pow2 h := by
    simpa [h, yp] using block_residual_lt y
  have hstep : yp * pow2 g + xp < (yp + 1) * pow2 g := by
    rw [Nat.add_mul]
    have hpos : 0 < pow2 g := pow2_pos g
    omega
  have hle : (yp + 1) * pow2 g ≤ pow2 h * pow2 g := by
    exact Nat.mul_le_mul_right (pow2 g) (Nat.succ_le_of_lt hy)
  have hpow : pow2 (g + h) = pow2 h * pow2 g := by
    unfold pow2
    rw [Nat.add_comm, Nat.pow_add]
  rw [hpow]
  exact Nat.lt_of_lt_of_le hstep hle

theorem shellPos_lt_shellSize (x y : Nat) :
    shellPos x y < shellSize (len x + len y) := by
  let g := len x
  let h := len y
  let s := g + h
  have htail : (y - blockStart h) * pow2 g + (x - blockStart g) < pow2 s := by
    simpa [g, h, s] using shellTail_lt x y
  have hg : g < s + 1 := by
    omega
  have hcalc :
      g * pow2 s + ((y - blockStart h) * pow2 g + (x - blockStart g))
        < (s + 1) * pow2 s := by
    calc
      g * pow2 s + ((y - blockStart h) * pow2 g + (x - blockStart g))
        < g * pow2 s + pow2 s := by
          exact Nat.add_lt_add_left htail (g * pow2 s)
      _ = (g + 1) * pow2 s := by
          rw [Nat.add_mul, Nat.one_mul]
      _ ≤ (s + 1) * pow2 s := by
          exact Nat.mul_le_mul_right (pow2 s) (Nat.succ_le_of_lt hg)
  simpa [shellPos, shellSize, g, h, s, Nat.add_assoc] using hcalc

theorem shellStart_succ (s : Nat) :
    shellStart (s + 1) = shellStart s + shellSize s := by
  rfl

theorem shellStartClosed_eq_shellStart (s : Nat) :
    shellStartClosed s = shellStart s := by
  induction s with
  | zero =>
      rfl
  | succ s ih =>
      rw [shellStart_succ, ← ih]
      cases s with
      | zero =>
          simp [shellStartClosed, shellSize, pow2]
      | succ s =>
          simp [shellStartClosed, shellSize, pow2, Nat.pow_succ, Nat.mul_two,
            Nat.two_mul, Nat.add_mul, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm]

theorem encodeFast_eq_encode (x y : Nat) : encodeFast x y = encode x y := by
  simp [encodeFast, encode, shellStartClosed_eq_shellStart]

theorem shellStart_add (s k : Nat) :
    shellStart (s + k) = shellStart s + shellGap s k := by
  induction k generalizing s with
  | zero =>
      simp [shellGap]
  | succ k ih =>
      calc
        shellStart (s + (k + 1)) = shellStart ((s + 1) + k) := by
          congr 1
          omega
        _ = shellStart (s + 1) + shellGap (s + 1) k := ih (s + 1)
        _ = shellStart s + shellGap s (k + 1) := by
          simp [shellGap, shellStart_succ, Nat.add_assoc]

theorem shellGap_zero (s : Nat) :
    shellGap 0 s = shellStart s := by
  have h := shellStart_add 0 s
  simpa [shellStart] using h.symm

theorem locateShellFromCore_sound (sn : Nat × Nat) :
    let sp := locateShellFromCore sn
    sp.2 < shellSize sp.1 := by
  fun_induction locateShellFromCore sn with
  | case1 s n h =>
      simp [h]
  | case2 s n h ih =>
      simpa using ih

theorem locateShellFrom_sound (s n : Nat) :
    let sp := locateShellFrom s n
    sp.2 < shellSize sp.1 := by
  exact locateShellFromCore_sound (s, n)

theorem shellStart_locateShellFromCore (sn : Nat × Nat) :
    let sp := locateShellFromCore sn
    shellStart sp.1 + sp.2 = shellStart sn.1 + sn.2 := by
  fun_induction locateShellFromCore sn with
  | case1 s n h =>
      rfl
  | case2 s n h ih =>
      change shellStart (locateShellFromCore (s + 1, n - shellSize s)).1
          + (locateShellFromCore (s + 1, n - shellSize s)).2
        = shellStart s + n
      rw [ih]
      have hsle : shellSize s ≤ n := Nat.le_of_not_gt h
      rw [shellStart_succ]
      omega

theorem locateShellFromCore_gap (s k p : Nat) (hp : p < shellSize (s + k)) :
    locateShellFromCore (s, shellGap s k + p) = (s + k, p) := by
  induction k generalizing s with
  | zero =>
      have hp0 : p < shellSize s := by
        simpa using hp
      simp only [shellGap, Nat.add_zero]
      rw [locateShellFromCore]
      simp [hp0]
  | succ k ih =>
      have hnot :
          ¬shellSize s + shellGap (s + 1) k + p < shellSize s := by
        omega
      simp only [shellGap]
      rw [locateShellFromCore]
      simp [hnot]
      change locateShellFromCore
          (s + 1, shellSize s + shellGap (s + 1) k + p - shellSize s)
        = (s + (k + 1), p)
      rw [show shellSize s + shellGap (s + 1) k + p - shellSize s
          = shellGap (s + 1) k + p by omega]
      have htarget : s + (k + 1) = (s + 1) + k := by
        omega
      have hp' : p < shellSize ((s + 1) + k) := by
        simpa [htarget] using hp
      simpa [htarget] using ih (s + 1) hp'

theorem locateShell_of_bounds {s n : Nat}
    (hl : shellStart s ≤ n) (hu : n < shellStart (s + 1)) :
    locateShell n = (s, n - shellStart s) := by
  let p := n - shellStart s
  have hrec : shellStart s + p = n := by
    exact Nat.add_sub_of_le hl
  have hp : p < shellSize s := by
    rw [shellStart_succ] at hu
    omega
  have hgap : shellGap 0 s = shellStart s := shellGap_zero s
  unfold locateShell locateShellFrom
  change locateShellFromCore (0, n) = (s, p)
  rw [← hrec, ← hgap]
  simpa [p, Nat.zero_add] using
    locateShellFromCore_gap 0 s p (by simpa [Nat.zero_add] using hp)

theorem decodeInShell_eq_decode_of_bounds {s n : Nat}
    (hl : shellStartClosed s ≤ n)
    (hu : n < shellStartClosed (s + 1)) :
    decodeInShell s (n - shellStartClosed s) = decode n := by
  have hloc : locateShell n = (s, n - shellStart s) := by
    exact locateShell_of_bounds
      (s := s) (n := n)
      (by simpa [shellStartClosed_eq_shellStart] using hl)
      (by simpa [shellStartClosed_eq_shellStart] using hu)
  simp [decode, hloc, shellStartClosed_eq_shellStart]

/--
Unfinished optimization proof: the closed `clw` formula must select exactly
the shell containing `n`.
-/
theorem clw_shell_bounds (n : Nat) :
    shellStartClosed (clw n) ≤ n ∧ n < shellStartClosed (clw n + 1) := by
  sorry

/--
The non-recursive decoder agrees with the proved shell-scan decoder, once the
open arithmetic shell-bound proof for `clw` is supplied.
-/
theorem decodeFast_eq_decode (n : Nat) : decodeFast n = decode n := by
  unfold decodeFast
  exact decodeInShell_eq_decode_of_bounds
    (s := clw n) (n := n) (clw_shell_bounds n).1 (clw_shell_bounds n).2

theorem decodeInShell_encodeInShell (x y : Nat) :
    let g := len x
    let h := len y
    let s := g + h
    decodeInShell s (shellPos x y) = (x, y) := by
  let g := len x
  let h := len y
  let s := g + h
  let xp := x - blockStart g
  let yp := y - blockStart h
  have hxlt : xp < pow2 g := by
    simpa [g, xp] using block_residual_lt x
  have htail : yp * pow2 g + xp < pow2 s := by
    simpa [g, h, s, xp, yp] using shellTail_lt x y
  have hdivS :
      (g * pow2 s + (yp * pow2 g + xp)) / pow2 s = g :=
    mul_add_div_of_lt (pow2_pos s) htail
  have hmodS :
      (g * pow2 s + (yp * pow2 g + xp)) % pow2 s = yp * pow2 g + xp :=
    mul_add_mod_of_lt htail
  have hmodG : (yp * pow2 g + xp) % pow2 g = xp :=
    mul_add_mod_of_lt hxlt
  have hdivG : (yp * pow2 g + xp) / pow2 g = yp :=
    mul_add_div_of_lt (pow2_pos g) hxlt
  have hsub : s - g = h := by
    omega
  have hxrec : blockStart g + xp = x := by
    simpa [g, xp] using block_recompose x
  have hyrec : blockStart h + yp = y := by
    simpa [h, yp] using block_recompose y
  simp [decodeInShell, shellPos, g, h, s, xp, yp, Nat.add_assoc,
    hdivS, hmodS, hmodG, hdivG, hsub, hxrec, hyrec]

theorem locateShell_encode (x y : Nat) :
    locateShell (encode x y) = (len x + len y, shellPos x y) := by
  let s := len x + len y
  let p := shellPos x y
  have hp : p < shellSize s := by
    simpa [s, p] using shellPos_lt_shellSize x y
  have hgap : shellGap 0 s = shellStart s := shellGap_zero s
  unfold locateShell locateShellFrom encode
  change locateShellFromCore (0, shellStart s + p) = (s, p)
  rw [← hgap]
  simpa [Nat.zero_add] using
    locateShellFromCore_gap 0 s p (by simpa [Nat.zero_add] using hp)

/-- The simplified pairing decoder is a left inverse of the encoder. -/
theorem decode_encode (x y : Nat) : decode (encode x y) = (x, y) := by
  unfold decode
  rw [locateShell_encode x y]
  exact decodeInShell_encodeInShell x y

theorem encode_decodeInShell {s p : Nat} (hp : p < shellSize s) :
    encode (decodeInShell s p).1 (decodeInShell s p).2 = shellStart s + p := by
  let g := p / pow2 s
  let q := p % pow2 s
  let xp := q % pow2 g
  let yp := q / pow2 g
  let x := blockStart g + xp
  let y := blockStart (s - g) + yp
  have hg : g ≤ s := by
    simpa [g] using div_pow2_le_shell (s := s) (p := p) hp
  have hq : q < pow2 s := by
    simpa [q] using Nat.mod_lt p (pow2_pos s)
  have hxlt : xp < pow2 g := by
    simpa [xp] using Nat.mod_lt q (pow2_pos g)
  have hylt : yp < pow2 (s - g) := by
    simpa [g, q, yp] using div_pow2_lt_pow2_sub (s := s) (g := g) (q := q) hg hq
  have hlenx : len x = g := by
    simpa [x, xp] using len_block (g := g) (r := xp) hxlt
  have hleny : len y = s - g := by
    simpa [y, yp] using len_block (g := s - g) (r := yp) hylt
  have hsadd : g + (s - g) = s := Nat.add_sub_of_le hg
  have hxsub : x - blockStart g = xp := by
    simp [x]
  have hysub : y - blockStart (s - g) = yp := by
    simp [y]
  have hqrec : yp * pow2 g + xp = q := by
    calc
      yp * pow2 g + xp = pow2 g * yp + xp := by rw [Nat.mul_comm yp (pow2 g)]
      _ = q := by
        simpa [yp, xp, q] using Nat.div_add_mod q (pow2 g)
  have hprec : g * pow2 s + q = p := by
    calc
      g * pow2 s + q = pow2 s * g + q := by rw [Nat.mul_comm g (pow2 s)]
      _ = p := by
        simpa [g, q] using Nat.div_add_mod p (pow2 s)
  simp [decodeInShell, encode, shellPos, g, q, xp, yp, x, y,
    hlenx, hleny, hsadd, hxsub, hysub, hqrec, hprec, Nat.add_assoc]

theorem shellStart_locateShell (n : Nat) :
    let sp := locateShell n
    shellStart sp.1 + sp.2 = n := by
  have h := shellStart_locateShellFromCore (0, n)
  change shellStart (locateShellFromCore (0, n)).1
      + (locateShellFromCore (0, n)).2 = n
  simpa [shellStart] using h

/-- The simplified pairing encoder is a right inverse of the decoder. -/
theorem encode_decode (n : Nat) : encode (decode n).1 (decode n).2 = n := by
  unfold decode
  generalize hsp : locateShell n = sp
  have hs : sp.2 < shellSize sp.1 := by
    rw [← hsp]
    exact locateShellFrom_sound 0 n
  have hoff : shellStart sp.1 + sp.2 = n := by
    simpa [hsp] using shellStart_locateShell n
  rw [encode_decodeInShell hs, hoff]

/--
The executable closed-form encoder and decoder form the same bijection as
`iso`, modulo the remaining open arithmetic proof `clw_shell_bounds`.
-/
def isoFast : (Nat × Nat) ≃ᵢ Nat where
  toFun p := encodeFast p.1 p.2
  invFun := decodeFast
  left_inv := by
    intro p
    cases p with
    | mk x y =>
        change decodeFast (encodeFast x y) = (x, y)
        rw [decodeFast_eq_decode, encodeFast_eq_encode, decode_encode]
  right_inv := by
    intro n
    change encodeFast (decodeFast n).1 (decodeFast n).2 = n
    rw [decodeFast_eq_decode, encodeFast_eq_encode, encode_decode]

/-- The proved shell-based pairing function, packaged as a bijection. -/
def iso : (Nat × Nat) ≃ᵢ Nat where
  toFun p := encode p.1 p.2
  invFun := decode
  left_inv := by
    intro p
    cases p with
    | mk x y =>
        exact decode_encode x y
  right_inv := encode_decode

end Pairing
end BijForm
