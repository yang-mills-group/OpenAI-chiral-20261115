import YM.CF.Buffered.PushMark
import YM.CF.Continuum.Canal

/-! # Physical buffer

Pay the manuscript's example choice `r₁=100 L(1+R)` with the actual
one-step adjunction. Takes given r₂ bounding loomloc radii, and ℓ > 4 r₃
as specified; no further restrictions on patch J. We use a LOOSER patch
estimate (10 times patch radius) than the volume proof; the buffer still
suffices on the two opposite halves, maintaining at least ℓ at EVERY step.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Buffered
open Function Fock NormedSpace SU Lat Lattice Cube Finset MeasureTheory Branch Reflect Window Wilson Rush Peaks Scroll
open Phase Skye Pastry Tulip Dial Paige Push.SectorMeasure Scree RG Vault Fir Tree Next.SectorChange Girt Spire Stencil Advance
open scoped Topology BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N P : Side} (i : Axis) (s : ℤ)
lemma band_root (G : Ratio N P) {w : ℕ} (x : Seat N) (h : x∈ band N i s w) :
    (ratio G).embed x∈ band P i (G.count.val*s) (G.count.val*w) := by
  let A:= ratio G; let b : Seat N:= wrap (More N) (s • step i)
  let t:ℤ := G.count.val*s
  have hb:b i=(s:Per (More N)):=by simp [b]
  have hx:A.embed b i=(t:Per (More P)):=by rw [show A.embed b=_ from Ratio.embed_wrap A (s • step i)]; simp [t,A,wrap_here]; rfl
  have hu:(A.embed x i-(t:Per (More P))).val=G.count.val* (x i-(s:Per (More N))).val := by
     have he:= embed_nat_ax i A (x-b); rw [←Ratio.root_embed, map_sub] at he; change (A.embed x i-A.embed b i).val=G.count.val* (x i-b i).val at he; rwa [hb,hx] at he
  apply (band_spec i t _ _).mpr; change _≤(A.embed x i - (t:Per (More P))).val ∧ (A.embed x i-(t:Per (More P))).val+_≤_
  obtain ⟨p,k⟩:= (band_spec i s w x).mp h; rw [hu,← mul_add,G.exact_size,Nat.mul_comm N.val]; exact ⟨Nat.mul_le_mul_left _ p,Nat.mul_le_mul_left _ k⟩
lemma band_pad {w u R : ℕ} (h : u+R ≤ w) : halo R (band N i s w) ⊆ band N i s u := by
  intro x hx; obtain ⟨y,v,p⟩:= halo_spec.mp hx; obtain ⟨p₁,p₂⟩:= (band_spec ..).mp v
  have he := (component_le (x-y) i).trans ((separation_comm x y).trans_le p); let k := Lattice.lift (x-y) i; change k.natAbs ≤ R at he
  let a : Per (More N) := y i-s; let r := a.val; change w ≤ r at p₁; change r+w ≤ _ at p₂
  have hg : 0 ≤ k + r := by omega
  have ht:k+r < (More N).val:=by have ht:0<N.val:= N.property; change k+r< ↑(N.val*2); omega
  have hz:x i-(s:Per (More N))= ((k+r:ℤ):Per (More N)) := by
    rw [Int.cast_add, Int.cast_natCast, show (r:Per (More N))=a from ZMod.natCast_zmod_val _, show (k:Per (More N))=x i-y i from ZMod.coe_valMinAbs _]; unfold a; abel
  apply (band_spec ..).mpr; rw [hz, show (ZMod.val ((k+r:ℤ):Per (More N)))=_ from ?_]
  show u ≤ (k+r : ℤ).toNat ∧ _ ; omega
  rw [show ((k+r:ℤ):Per (More N))=((k+r:ℤ).toNat:Per (More N)) by exact (congrArg (Int.cast : ℤ → Per (More N)) (Int.toNat_of_nonneg hg).symm).trans (Int.cast_natCast _), ZMod.val_natCast_of_lt (show (k+r:ℤ).toNat < (More N).val from by omega)]

lemma across_coord (x : Seat N) : (plane i s).anon N x i-(s:Per (More N))= -(x i-(s:Per (More N))) := by
  simp [plane, Shape.anon, affine, Signed.mirror,Signed.act,wrap_here,two_mul]; abel
lemma opposite_gap {u : ℕ} (v : 0<u) (x y : Seat N) (hx : x∈ band N i s u) (p : y∈ (band N i s u).image ((plane i s).anon N)) : 2*u ≤ separation x y := by
  obtain ⟨y,h,rfl⟩:= mem_image.mp p; let a:Per (More N):=x i-s; let b:Per (More N):=y i-s
  have hc: u ≤ a.val ∧ a.val+u ≤ N.val := (band_spec ..).mp hx; have hb:u ≤ b.val ∧ b.val+u ≤ N.val:= (band_spec ..).mp h
  let z:=(plane i s).anon N y
  apply Nat.le_trans _ (component_le (x-z) i); unfold Lattice.lift; rw [Pi.sub_apply, show x i-z i= ((a.val+b.val:ℕ):Per (More N)) from ?_]; swap
  · have he:= across_coord i s y; change z i-(s:Per (More N)) = -b at he; rw [Nat.cast_add,ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,eq_add_of_sub_eq he]; unfold a; abel
  have he : (More N).val=N.val*2:= rfl; rw [ZMod.valMinAbs_natAbs_eq_min,ZMod.val_natCast_of_lt (show _ from (by omega : a.val+b.val<(More N).val))]; omega

-- gaugeM example, any no smaller choice
variable (L : Side)
def r₁ (L : Side) (R : ℕ) := 100 * L.val * (1+R)
def r₃ (L : Side) (R w J : ℕ) := 4*(r₁ L R + w + J + 10)
abbrev Margin (L : Side) (R w J e : ℕ) := 4*r₃ L R w J < e
variable {L} {R w J e : ℕ} (g : Margin L R w J e)
private lemma before_cost : beforePad R ≤ r₁ L R := by have he:0<L.val:= L.property; unfold r₁ beforePad; nlinarith
include g
lemma margin_step (k : 3 ≤ L.val) : e+L.val*gross R w J ≤ L.val*e := by
  have ht:= before_cost (L:=L) (R:=R); unfold Margin r₃ at g; unfold gross; nlinarith
lemma margin_separate (x y : Seat N) (p : x∈ (band N i s e).image ((plane i s).anon N)) (q : y ∈ band N i s e) : 2*(nearZero R+w)<separation x y := by
  have ht:= before_cost (L:=L) (R:=R); unfold Margin r₃ at g; have he:= opposite_gap i s (Nat.zero_le _|>.trans_lt g) y x q p; rw [separation_comm]; unfold beforePad nearZero at *; omega
lemma margin_band (G : Ratio N P) (h : G.count=L) (k : 3≤ L.val) :
    padded G (band N i s e) (G.count.val * gross R w J) ⊆ band P i (L.val*s) e := by
  have he : (band N i s e).image (ratio G).embed ⊆ band P i (L.val*s) (L.val*e) := by
    intro i' hx; obtain ⟨x,p,rfl⟩:= mem_image.mp hx; rw [←h]; exact band_root i s G _ p
  unfold Advance.padded; rw [h]; exact Subset.trans (Corona.halo_mono le_rfl he) (band_pad i (L.val*s) (margin_step g k))
end YM.CF.Buffered
