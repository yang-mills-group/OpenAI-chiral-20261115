import YM.CF.BProof.Nest.Room
import YM.CF.BProof.Nest.Wool
import YM.CF.BProof.Nest.Paint
/-! Native palette papers. Uniform holder costs, absolute payments θ. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mesh.Nest
open Stave Filter Function Metric Lattice Wilson Finset
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators NNReal Classical
variable {n:Side}{q s:ℕ}{d:ℝ}
abbrev Vent(n:Side):= Site n → Lattice.Order
local notation "Sκ"=>Site n
local notation "G_"=>SU.group
local notation "L_"=>Nerve.Halo
local notation "K_"=>Nerve.King
namespace Wool
variable (W:Wool n q)(O:Vent n)(U:Config SU.group n)
local notation "A_"=> W.wheel
def spr (x i:Sκ):ℝ:= Real.sqrt (A_ x i)
def peg (x i:Sκ): plate (Floor q) := btl (W.hue i) (W.spr x i • SU.fund (Wire i (O i) U x))
def native (x:Sκ): Attic q:= ∑ i,W.peg O U x i
local notation "πκ"=> W.peg O U
lemma peg0 {x i:Sκ}(u: i∉ W.group x): πκ x i=0:=by rw [peg,spr,Wool.vani u,Real.sqrt_zero,zero_smul,btl_zero]
lemma subtotal(x:Sκ)(S:Support n)(h:W.group x ⊆ S): W.native O U x= ∑ i∈S, πκ x i:= Eq.symm (sum_subset (subset_univ _) (fun i _ p=> peg0 W O U (fun g=>p (h g))))
variable {W} (t:W.Rub s d)
include t
lemma rub_sum (x:Sκ): ∑ i∈W.group x, W.wheel x i=1:= (sum_subset (subset_univ _) (fun i _ h=>vani h)).trans (t.deals x).mass
lemma ziss (x i:Sκ): 0≤ W.spr x i ∧ W.spr x i≤1∧ W.spr x i^2=W.wheel x i:= by
 have p:= (t.deals x).pos i; refine ⟨Real.sqrt_nonneg _,?_,Real.sq_sqrt p⟩; exact (Real.sqrt_le_sqrt ((t.deals x).bounded i)).trans_eq Real.sqrt_one
lemma frame(x:Sκ): native W O U x∈ King (Floor q):=by
 let S:= W.group x; rw [subtotal W O U x S (Subset.refl _)]; change (∑ i∈ S, πκ x i)ᴴ *(∑ i∈ S, πκ x i)=1
 have hk:Set.InjOn W.hue S:= by have h:=t.distinct x x (by simp); exact h.mono (subset_union_left)
 have hv(i) (p:i∈S) : (πκ x i)ᴴ * (∑ j∈S,πκ x j)=W.wheel x i • 1:=by
    rw [Matrix.mul_sum, sum_eq_single i (fun j hj hi=> by rw [peg,peg,bond, if_neg (fun he=>hi (hk hj p he.symm))]) (by simp [p])]; rw [peg,bond,if_pos rfl,Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul,smul_smul, (show (SU.fund _)ᴴ * SU.fund _ =1 from SU.group.mat_star_mul (Wire i (O i) U x)), ← sq, (ziss t x i).2.2] -- tune def
 rw [Matrix.conjTranspose_sum,Matrix.sum_mul, sum_congr rfl hv,← Finset.sum_smul,rub_sum t x,one_smul]

omit t in
lemma root_shift{A B d:ℝ} (h:0≤A)(g:0≤B)(p:|A-B|≤d): |Real.sqrt A-Real.sqrt B|≤Real.sqrt d:=by
 have hx: 0≤ d:=(abs_nonneg _).trans p
 let K:=Real.sqrt; have H(A B)(h:0≤A)(g:0≤B)(p:A-B≤d): K A-K B ≤ K d:=by have f₁:=Real.sq_sqrt h; have f₂:=Real.sq_sqrt g; have f₃:=Real.sq_sqrt hx; unfold K; nlinarith [Real.sqrt_nonneg A,Real.sqrt_nonneg B,Real.sqrt_nonneg d]
 rw [abs_le]; exact ⟨by linarith only [show Real.sqrt B-Real.sqrt A ≤ Real.sqrt d from H B A g h ((le_abs_self _).trans (abs_sub_comm A B ▸ p))],H A B h g ((le_abs_self _).trans p)⟩ -- t binder error
abbrev cash(d u:ℝ):ℝ:=3*u+3*Real.sqrt d
lemma tilt{u δ:ℝ}(u':0≤δ) (o:0<s) (p:Nerve.SmallN s n) (h:Law G_ u δ (K_*s))(x:Sκ)(j:Axis)(g: ∀ i∈ W.group x,Clear u (K_*s) U i)(i:Sκ): dist (roll (peg W O U x i) (U (x,j))) (peg W O U (x+step j) i)≤ cash d δ:=by
 let y:= x+step j; let A:= W.spr x i; let B:=W.spr y i; let V:= Wire i (O i) U x* U (x,j); let Y:= Wire i (O i) U y; let s₅:=SU.group.colorScale
 have hy:|A-B|≤ Real.sqrt d:= root_shift (t.deals x|>.pos i) (t.deals y|>.pos i) (t.decal x y (nearV x (posDir j)) i); have hiᵥ:0≤A:= (ziss t x i).1; have hib:0≤B:= (ziss t y i).1
 rw [peg,peg,beam_roll,beam_dist]; change dist ((A • _) * _) (B • SU.fund Y)≤_; rw [Matrix.smul_mul]; change dist (A • SU.fund V) (B • SU.fund Y) ≤_
 have hk(f:SU.E): ‖SU.fund f‖≤3:= king_le (unit_su f)
 have hz(V: SU.E): dist (A • SU.fund V) (B • SU.fund V) ≤ 3*Real.sqrt d:= by rw [dist_eq_norm,←sub_smul,norm_smul,Real.norm_eq_abs,mul_comm]; exact mul_le_mul (hk _) hy (abs_nonneg _) (by norm_num)
 have hp:3*Real.sqrt d ≤ cash d δ:=by unfold cash; linarith
 by_cases e:i∈ W.group x
 · by_cases w:i∈ W.group y
   · have he:cd SU.group V Y ≤δ:=duct h p o U _ _ _ (g _ e) (t.mom _ _ e) (t.mom _ _ w) -- mom x i already! tune
     refine (dist_triangle _ (A • SU.fund Y) _).trans (add_le_add ?_ (hz Y)); rw [dist_eq_norm,← smul_sub,norm_smul,Real.norm_of_nonneg hiᵥ]; apply (mul_le_of_le_one_left (norm_nonneg _) (ziss t x i).2.1).trans; have ht:= (norm_le_scale ..).mp he; change ‖SU.fund V-SU.fund Y‖≤δ*s₅ at ht; exact ht.trans (by rw [mul_comm]; gcongr; exact (G_size (unit_su V)).symm.trans_le (hk V))
   rw [show B=0 from by unfold B spr; rw [vani w, Real.sqrt_zero]] at *; simpa using (hz V).trans hp
 rw [show A=0 from by unfold A spr; rw [vani e, Real.sqrt_zero]] at *; simpa using (hz Y).trans hp
-- coarse
lemma along {u δ:ℝ}(u':0≤δ) (o:0<s) (p:Nerve.SmallN s n) (h:Law G_ u δ (K_*s))(x:Sκ)(j:Axis)(g: ∀ i∈ W.group x,Clear u (K_*s) U i): dist (roll (W.native O U x) (U (x,j))) (W.native O U (x+step j)) ≤ 5 * cash d δ:=by
 let S:=W.both x (x+step j); rw [subtotal W O U x S subset_union_left,subtotal W O U _ S subset_union_right]; unfold roll; rw [Matrix.sum_mul,dist_eq_norm,← sum_sub_distrib]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=>cash d δ) (fun i _=>?_)).trans ?_)
 · rw [←dist_eq_norm]; exact tilt O U t u' o p h x j g i -- tune
 rw [sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right _ (by unfold cash; positivity); exact_mod_cast (t.mar x (x+step j) (nearV x (posDir j)):(S.card:ℕ)≤5)
end Wool
end YM.CF.BProof.Mesh.Nest
