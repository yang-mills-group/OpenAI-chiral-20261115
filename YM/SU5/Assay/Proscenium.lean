import YM.SU5.Assay.Premiere
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 360000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock
namespace Etch
open Analysis Heat

/-! Checker sizing and separation with unbounded offsets and wraps. -/
abbrev pitch (B:Side)(w:ℕ):ℕ:=16*B.val*w
lemma pitch_pos (B:Side){w:ℕ}(h:0<w):0<pitch B w:=mul_pos (mul_pos (by decide) B.property) h
lemma pitch_cast (B:Side)(w:ℕ): ((pitch B w:ℕ):ℤ)=ruler B * w:=by unfold pitch ruler; push_cast; rfl

structure Proscenium (B:Side)(w:ℕ)(N:Side)(r:ℕ):Prop where
  wid : 0<w
  pos : 0<r
  low : pitch B w * (4*r)≤(More N).val
  high : (More N).val ≤ 2*pitch B w*(4*r)
variable {B N:Side}{w p r:ℕ}
lemma proscenium (hw:0<w)(h: 2*pitch B w≤N.val): Proscenium B w N (finalN N.val (pitch B w)):=by
 let t:=2*pitch B w; have ht:0<t:=mul_pos two_pos (pitch_pos B hw)
 let r:=N.val/t; have f:0<r:=Nat.div_pos h ht
 have x : r*t≤N.val:=Nat.div_mul_le_self ..
 have y:N.val<(r+1)*t:=Nat.lt_mul_div_succ _ ht |>.trans_eq (Nat.mul_comm ..)
 have u:(r+1)*t≤(r+r)*t:=Nat.mul_le_mul_right _ (by omega)
 apply Proscenium.mk hw f
 · change pitch B w*(4*r)≤ N.val*2
   rw [show pitch B w*(4*r)=r*t*2 from by unfold t; ring]
   exact Nat.mul_le_mul_right 2 x
 change N.val*2 ≤ 2*pitch B w*(4*r)
 exact le_trans (Nat.mul_le_mul_right _ (y.le.trans u)) (le_of_eq (by unfold t; ring))
section
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)
include V Q
lemma proscenium_at (hw:0<w):∀ᶠ e:ℕ in atTop,
 Proscenium Λ.block w (Journey.side Y (i (a e)) s) (slideN Y s w (i (a e))):=by
 filter_upwards [(site_law Y H V Q s).eventually_ge_atTop (2*pitch Λ.block w)] with e h
 exact proscenium hw h
end

abbrev ratio (B:Side)(w:ℕ):ℕ:=128*pitch B w^4
lemma ratio_pos (B:Side){w:ℕ}(hw:0<w):0<ratio B w:=mul_pos (by decide) (pow_pos (pitch_pos B hw) _)
lemma Proscenium.density (h:Proscenium B w N r)(x:Full r p):
   (More N).val^4 ≤ ratio B w*p:=by
 apply (pow_le_pow_left' h.high 4).trans
 rw [mul_pow]
 exact le_trans (Nat.mul_le_mul_left _ x.1) (le_of_eq (by unfold ratio; ring))
lemma Proscenium.density' (h:Proscenium B w N r)(x:Full r p):
   ((ratio B w:ℕ):ℝ)⁻¹*Py.Rate.sites N ≤ (p:ℝ):=by
 rw [inv_mul_le_iff₀ (show 0<((ratio B w:ℕ):ℝ) by exact_mod_cast ratio_pos B h.wid)]
 unfold Py.Rate.sites; exact_mod_cast h.density x

variable {K:Calibration}{σ x y l h:Cover}
local notation "R"=> runnel K w σ
/-- Tile x at margin D (in gauge units). -/
def Inset (K:Calibration)(w:ℕ)(σ x:Cover)(D:ℕ)(a:Cover):Prop:=
 ∀i,runnel K w σ i (x i)+D ≤ a i∧ a i+D ≤ runnel K w σ i (x i+1)
variable {D:ℕ}{a c:Cover}

private lemma sepAxis (i:Axis)(hD : (D:ℤ) ≤ c i-a i)(hD':c i-a i ≤ ((More N).val:ℤ)-D):
    D ≤ separation (wrap (More N) c) (wrap (More N) a):=by
 set T:= wrap (More N) c -wrap (More N) a
 let P:= lift T i
 suffices D ≤ P.natAbs from this.trans (component_le T i)
 by_contra! v
 have t: ((More N).val:ℤ)∣ c i-a i-P:=
   (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp <| congrFun (show wrap (More N) (lift T)=wrap (More N) (c-a) from by rw [wrap_lift,map_sub]) i
 have h : 0<c i-a i-P:=by omega
 have z:=Int.le_of_dvd h t; omega

private lemma Inside_gap (t:Proscenium K.B w N r)(hr:Hall r l h)(v:Inbox l h x)(u:Inbox l h y)
    (A:Inset K w σ x D a)(C:Inset K w σ y D c)(i:Axis)(hx:x i < y i):
    2*D ≤ separation (wrap (More N) c) (wrap (More N) a):=by
 have f:=A i; have g:= C i; have R₁:=v i; have R₂:= u i; have h:=hr i
 have hw:0≤ (w:ℤ):=by positivity
 apply sepAxis i
 · have q:=runnelMono K _ σ hw i (show x i+1≤ y i by omega) -- order
   push_cast; omega
 have hz:=mul_le_mul_of_nonneg_left (show y i+1-x i≤4*(r:ℤ) by omega) (mul_nonneg (ruler_gene K.B).le hw)
 have hp:= t.low
 have he: ((pitch K.B w*(4*r):ℕ):ℤ) ≤ ↑(More N).val:=by exact_mod_cast hp
 have hi:runnel K w σ i (y i+1)-runnel K w σ i (x i) ≤ ↑(More N).val:=by
   apply le_trans _ he
   unfold runnel pitch ruler at *; push_cast; linarith only [hz]
 rw [Nat.cast_mul,Nat.cast_ofNat]; omega

lemma Proscenium.separation_le (t:Proscenium K.B w N r)(hr:Hall r l h)(v:Inbox l h x)(u:Inbox l h y)(hx:x≠y)
    (A:Inset K w σ x D a)(C:Inset K w σ y D c):
   2*D ≤ separation (wrap (More N) a) (wrap (More N) c):=by
 have ht:¬∀i,x i=y i:=fun e=>hx (funext e)
 obtain ⟨i,h⟩:=not_forall.mp ht
 rcases lt_or_gt_of_ne h with e|e
 · rw [separation_comm]; exact Inside_gap t hr v u A C i e
 exact Inside_gap t hr u v C A i e

lemma Proscenium.disjoint {S T:Finset Cover}(t:Proscenium K.B w N r)(hr:Hall r l h)(v:Inbox l h x)(u:Inbox l h y)(hx:x≠y)
    (A:House K w σ x S)(C:House K w σ y T):
    Disjoint (Satin.region S N) (Satin.region T N):=by
 apply disjoint_left.mpr
 intro i m n; obtain ⟨a,g,h⟩:= mem_image.mp m; obtain ⟨c,f,j⟩:=mem_image.mp n
 have ht:=t.separation_le hr v u hx (D:=K.ℓ) (a:=a) (c:=c) (σ:=σ) (fun i=>A i a g) (fun i=>C i c f)
 rw [h,j,separation_self] at ht
 have he: 0<K.ℓ:=(Nat.zero_le _).trans_lt K.buffer
 omega
end Etch
end YM.CF.Buffered.Afterglow.Tower.SlabMark
