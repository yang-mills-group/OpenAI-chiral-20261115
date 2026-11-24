import YM.CF.BProof.Nest.Era
/-! Support bounds for equation fd-V. Translation uses Plan.n. Charge with Spire tapes. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mesh.Nest
open Stave Filter Function Metric Lattice Wilson Finset
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators NNReal Classical
variable {n:Side}{q s:ℕ}{d u δ:ℝ}
local notation "Sκ"=>Site n
local notation "G_"=>SU.group
local notation "L_"=>Nerve.Halo
local notation "K_"=>Nerve.King
variable {W W':Wool n q}(t:W.Rub s d)(O O':Vent n){U V:Config SU.group n}
-- polar paint common
def dye (p:Bool){I J:Type*}(A:Matrix I J ℂ):= if p then blink A else A
lemma dye_2(p:Bool){I J:Type*}(A:Matrix I J ℂ):dye p (dye p A)=A:=by cases p <;> simp [dye]
lemma dye_sum (p:Bool){I J K:Type*} [Fintype K](F:K→Matrix I J ℂ):∑ i, dye p (F i)= dye p (∑ i,F i):=by
 ext i j :1; cases p <;> simp [dye, Matrix.sum_apply]
lemma dye_dist(p:Bool){I J:Type*}[Fintype I][Fintype J](A B:Matrix I J ℂ):dist (dye p A) (dye p B)=dist A B:=by cases p <;> simp [dye]
lemma dye_roll(p:Bool){I:Type*}(A:plate I)(u:SU.E):dye p (roll A u)=roll (dye p A) (Spire.polarT p u):=by cases p; rfl; exact blink_roll ..
namespace Wool
lemma mask_vals {S:Support n}{x:Sκ}(p:Set.EqOn W.mark W'.mark S)(u:x∈S): W.wheel x=W'.wheel x:= congrArg Prod.snd (p u)
lemma ranges {S:Support n}{x:Sκ}(p:Set.EqOn W.mark W'.mark S)(u:x∈S):W.group x=W'.group x:=by unfold group; rw [mask_vals p u]
lemma spun(e: Equiv.Perm Sκ)(p:Equates e W W')(x i:Sκ): i∈ W.group x↔ e i∈ W'.group (e x):=by simp only [group_in, p.2]
lemma sprj {S:Support n}{x:Sκ}(p:Set.EqOn W.mark W'.mark S)(u:x∈S) : W.spr x=W'.spr x:= by ext; unfold spr; rw [mask_vals p u]
abbrev keep0(s:ℕ):=5*(L_*s)
include t
lemma sees (x:Sκ)(a:Set.EqOn O O' (region n x (keep0 s)))(b:Set.EqOn W.mark W'.mark (region n x (keep0 s)))(p:Agrees (region n x (keep0 s)) U V): W.native O U x=W'.native O' V x:=by
 let R:=keep0 s; let S:= region n x R; have u:x∈S:= (reg_in ..).2 (by simp); let L:=W.group x; have k :W'.group x⊆L:= (ranges b u).symm.le
 rw [subtotal _ _ _ _ L (Subset.refl _),subtotal _ _ _ _ L k]; apply sum_congr rfl; intro i hi; have hu:L_*s ≤ R:= Nat.le_mul_of_pos_left _ (by decide); have hm:=t.mom x i hi; have hv:i∈S:= (reg_in ..).2 (hm.trans hu); have ht: separation x i ≤ L_*s:= hm; rw [peg,peg,sprj b u,show W.hue i=W'.hue i from congrArg Prod.fst (b hv),a hv]; congr 2; exact congrArg SU.fund (wire_cost (O' i) ht U V (agrees_mono p (reg_pay ht (by unfold keep0; omega)))) -- hm compare region ht x i; wire x b dist x i good; maybe needs congr at smul
omit t in
lemma vacuum_c (W:Wool n q)(x:Sκ): Continuous (fun U:Config SU.group n=> W.native O U x):= continuous_finsetSum _ (fun i _=>by unfold peg; exact ((Isometry.of_dist_eq (beam_dist _)).continuous.comp (show Continuous (fun U:Config G_ n=>W.spr x i • SU.fund (Wire i (O i) U x)) from (SU.fund_cont.comp (wire_cont i (O i) x)).const_smul (W.spr x i)))) -- actual goal native sum; library Cont
lemma pegs {p:Bool}{s':Signed}{o:Sκ}(S:Nerve.SmallN s n)(e:Equates (facet s' o) W W')(v:∀ i, O' (facet s' o i)= orderEquiv s' (O i))(x i:Sκ): peg W O (Opts s' o p U) x i=dye p (peg W' O' U (facet s' o x) (facet s' o i)):=by
 let y:=facet s' o; by_cases b:i∈ W.group x; swap; · rw [peg0 W _ _ b,peg0 W' _ _ ((spun y e x i).not.mp b)]; cases p <;> simp [dye]
 rw [peg,opt_mark S (t.mom x i b),peg,v]; unfold spr; rw [e.2,e.1]; cases p; rfl; simp only [dye,↓reduceIte,← Stave.blink_apply, beam_blink, Stave.blink_smul]
lemma n_rev {p:Bool}{s':Signed}{o:Sκ}(S:Nerve.SmallN s n)(e:Equates (facet s' o) W W')(v:∀ i, O' (facet s' o i)= orderEquiv s' (O i))(x:Sκ): W.native O (Opts s' o p U) x=dye p (W'.native O' U (facet s' o x)):=by
 unfold native; simp_rw [pegs t O O' S e v]; rw [dye_sum, Equiv.sum_comp]
end Wool
end YM.CF.BProof.Mesh.Nest
