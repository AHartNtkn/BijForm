import BijForm.Coding

namespace BijForm
namespace Pairing

/-
This module formalizes the simplified pairing function from the
"further simplification" section of "An Optimal And Feasible Pairing Function".
The blog presents the closed arithmetic expression

  (g + s - 2) * 2^s + y * 2^g + x + 2

after measuring `x` and `y` as binary strings.  Over `Nat`, the leading
integer offset is negative in the first shells, so the Lean definition uses the
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

def decode (n : Nat) : Nat × Nat :=
  let sp := locateShell n
  decodeInShell sp.1 sp.2

theorem pow2_pos (n : Nat) : 0 < pow2 n := by
  unfold pow2
  exact Nat.two_pow_pos n

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
  -- Pending proof work, tracked by BF-PAIRING-001: cumulative shell sizes place
  -- the encoding in exactly the shell determined by the two binary-string
  -- lengths.
  sorry

/-- The simplified pairing decoder is a left inverse of the encoder. -/
theorem decode_encode (x y : Nat) : decode (encode x y) = (x, y) := by
  unfold decode
  rw [locateShell_encode x y]
  exact decodeInShell_encodeInShell x y

theorem encode_decodeInShell {s p : Nat} (hp : p < shellSize s) :
    encode (decodeInShell s p).1 (decodeInShell s p).2 = shellStart s + p := by
  -- Pending proof work, tracked by BF-PAIRING-001: inverse arithmetic for group
  -- index and residual bits.
  sorry

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

/-- The simplified pairing function from the blog, packaged as a bijection. -/
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
