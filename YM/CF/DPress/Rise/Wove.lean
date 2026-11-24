import YM.CF.DPress.Rise.Stream
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour.Heath
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
open Exa Tap Dial
open Levier Thera Urn Nacre Salt
open Haro -- 
open LinQ Cad Mercer Room Push.AbsoluteSums Larch Ione Trees Py Wray Kay DPress.Fees DPress.Analytic Moral Flight Kernel Probe Docket
open scoped YM.CF.Mew
variable {N:Side}{P:BudgetPoint}{s t u v a b c h e ε H:ℝ}{q:ℕ}{F:Scree.Loom N}{D:Docket P}
namespace Docket
variable (D)
abbrev Singlet (U:Cusp N)(q:ℕ)(h:ℝ):Prop:= flame P q U ∧ PactF P (wu P) h (EmptyD U) (D.Sh/10)∧ XL P h (wu P) U (D.SF/10)
variable {D} {X Y: Cusp N}
structure Pair(h ε:ℝ)(X Y:Cusp N)(D:Docket P)(q:ℕ):Prop where
 gear0 : 0 ≤ ε
 last : ε ≤ 1
 first : D.Singlet X q h
 second : D.Singlet Y q h
 drain : PactF P (wu P) h (EmptyD Y-EmptyD X) (ε*(D.Sh/10))
 wrath : XL P h (wu P) (Y-X) (ε*(D.SF/10))
 equal : ε=0 → X=Y
abbrev ft(X Y:Cusp N)(L:ℝ)(z:ℂ) := Flight.vista Y X (Flight.keep L z)
abbrev Fβ(X:Cusp N)(Q:Cad.Θ)(v:Room F P e u h q)(T S:BeatL N)(A:BondL T S (body_Q 1) b c a e): Cusp N:= RiseB P X (v.J_Q A Q)
variable (E:D.Pair h ε X Y q) -- field dot ambiguous name structure Pair
include E
lemma starta : flame P q (Y-X):=by rw [sub_eq_add_neg,←neg_one_smul ℂ X]; exact lives_o _ _ E.second.1 (lives_z _ E.first.1 _)
lemma xtend (ht:1≤h)(l:ℝ)(z:ℂ)(g:‖Flight.keep l z‖ * ε ≤ 2) : ∃ I:blazeK N,D.Account I∧bill P q h I (ft X Y l z):=by
 let t:= Flight.keep l z; have hu(w:ℝ)(h:0≤w):w/10+‖t‖*(ε*(w/10))≤w:=by have hz:= mul_le_mul_of_nonneg_right g h; change ‖t‖ * ε * w ≤ _ at hz; nlinarith only [hz,h] -- tune
 have he: EmptyD (ft X Y l z)= EmptyD X+t • (EmptyD Y-EmptyD X):=rfl; apply accountB0 _ (lives_o _ _ E.first.1 (lives_z _ (starta E) t)) ht; -- rw maybe.Benchmark.
 · rw [he]; let F:=fortune (n:=N) P h (wu P) ht; exact F.toReceipt.relax (F.add E.first.2.1 (F.scale t E.drain)) (hu D.Sh D.fundsE)
 let F:=νreg (n:=N) P h (wu P) true ht; exact F.toReceipt.relax (F.add E.first.2.2 (F.scale t E.wrath)) (hu D.SF D.fundsF)
-- pressure at common radius.Comparator Reach_S.pair
variable {T S: BeatL N}(A:BondL T S (body_Q 1) b c a e)(R:Room F P e u h q)
omit E
-- cheaper.Second equal w_y master.Bucket.
abbrev Νx (X:Cusp N)(t:Cad.Θ):= Colony P X (R.J_Q A t) (R.Z_Q A t)
local notation "Qz"=>cipherK q
variable (P_:D.Pair h ε X Y (cipherK q)) -- reuses Y binder..
variable (U V:ΘS t)(ht:0<t) (tι:D.Chip (μχ A h P ht)) -- actual standard bead.B.nu
abbrev EV(x:Cusp N)(y:Cad.Θ) :=RiseB P x (R.J_Q A y)
-- standalone structures.ALP1_diff
structure Deltas : Prop where
 zeroE : PactF P (ρL P) h (EmptyD (EV A R Y V.val)-EmptyD (EV A R X U.val)) (D.Γ * (Flight.debt V U ε))
 fullE : XL P h (ρL P) (EV A R Y V.val - EV A R X U.val) ((D.κ⁻¹*D.Γ) * (Flight.debt V U ε))
 feeE : PactF P (lev2 P) h (Νx A R Y V.val-Νx A R X U.val) (D.Nr * (Flight.debt V U ε))
include P_ ht tι
open QHol
lemma curvePower : Deltas (X:=X) (Y:=Y) (D:=D) (ε:=ε) A R U V:=by
 let Δ:=Flight.debt V U ε
 have he:=P_.gear0; have hf:= Flight.nn V U ht; obtain r|r:= (add_nonneg he hf).eq_or_lt
 · have p:ε=0:=by linarith
   have u:U=V:=by
      have g:Flight.hΔ V U=0:=by linarith
      apply Subtype.ext; exact (sub_eq_zero.mp (norm_eq_zero.mp ((Flight.balance V U ht).symm.trans (by rw [g,zero_mul])))).symm
   rw [p,u,P_.equal p]; have ht:Flight.debt V V 0=0:=by unfold Flight.debt Flight.hΔ; simp
   constructor<;> simp only [sub_self,ht,mul_zero] -- ambiguity duplicate h
   exact (fortune (n:=N) _ _ _ R.heil).zero_p
   exact (νreg (n:=N) _ _ _ true R.heil).zero_p
   exact (fortune (n:=N) _ _ _ R.heil).zero_p
 let l:=wideS V U ε; let J:=JΘ A R U V l; let F':= ft X Y l; let V':=ZΘ A R U V l
 have hv:1<l:= starV V U r
 have hm :HaloL l F':=by
    intro i j V; unfold F' ft Flight.vista; dsimp only; simp only [Pi.add_apply,Pi.smul_apply]; exact (differentiableOn_const _).add (keep_s.smul_const _)
 have ωK(z:ℂ): ‖Flight.keep l z‖*ε ≤ 2:=by
   have he': ‖Flight.keep l z‖*ε ≤ ε+1:=by
      have ht: l*ε = ε+Δ⁻¹*ε:=by unfold l wideS; ring
      apply (mul_le_mul_of_nonneg_right (keep_n z hv|>.le) he).trans; rw [ht]; refine add_le_add (le_refl ε) ?_; exact (inv_mul_le_iff₀ r).2 (by linarith)
   linarith only [he',P_.last]
 choose I kι fι using fun z:ℂ=> xtend P_ R.heil l z (ωK z)
 choose B Hp using fun i:ℂ=> Probe.backup A R U V ht r he i
 let C':= μχ A h P ht; let Θ'(i):=RiseB P (F' i) (J i); let f'(i):= Colony P (F' i) (J i) (V' i)
 have hν(i): Stax.Pitch P h (cipherK q) (J i) C' (B i):=Hp _
 have hz(k:ℝ): k/(l-1)=k*(Flight.debt V U ε):=by unfold l wideS; rw [add_sub_cancel_left]; simp only [div_eq_mul_inv,inv_inv] -- tune
 have ph(i:ℂ):= growth (kι i) tι R.heil (fι i) (Hp i); have hc:= QHol.halos F' J hm (faux A R U V ht) (fun z=>kι z) (fun z=>tι) R.heil fι hν -- '_'
 have fx:Θ' 0=EV A R X U.val:=by unfold Θ' F' ft J JΘ Flight.vista; rw [Flight.zero hv]; simp only [zero_smul,add_zero,EV]
 have fy:Θ' 1=EV A R Y V.val:=by unfold Θ' F' ft J JΘ Flight.vista; rw [Flight.one hv]; simp only [one_smul,add_sub_cancel,EV]
 have fz:f' 0=Νx A R X U.val:=by unfold f' V' ZΘ J F' ft JΘ Flight.vista; rw [Flight.zero hv]; simp only [zero_smul,add_zero,Νx]
 have fZ:f' 1=Νx A R Y V.val:=by unfold f' V' ZΘ J F' ft JΘ Flight.vista; rw [Flight.one hv]; simp only [one_smul,add_sub_cancel,Νx]
 constructor
 · rw [←hz,←fx,←fy]; exact wage_c P _ (ρL P) ℓZ R.heil (EmptyD∘ Θ') (fun z _=> (ph z).1) (fun i v _=>hc i ∅ (empty_subset _) v) hv -- expecting compile expensive
 · rw [←hz,←fx,←fy]; exact Ξcare P _ _ true R.heil ℓZ Θ' (fun z _=>(ph z).2) (fun i j p x _=>hc i j (mem_filter.mp p).2.2 x) hv
 rw [←hz,←fz,←fZ]; apply wage_c P h _ (Kay.Penny.levZero _) R.heil f' (fun i _=> strongN (kι i) tι R.heil (fι i) (Hp i) (V' i) (fun x j=> Probe.costB A R U V ht i j x)) _ hv; exact fun i y _=> QHol.logLp F' J hm (Probe.faux A R U V ht) (fun z=>kι z) (fun z=>tι) R.heil fι hν V' (fun i p=> Probe.Ξhr A R U V i p) i y -- tune parameters
end Docket
end YM.CF.Sour.Heath
