import GaugeFieldConstruction.Materia3
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 60000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry Grotto
namespace Ivey
open Sault Leaf Sour
open Ladder3 Drapes Tenant Palot Rue Iona
attribute [local instance] loreM loreN
variable {n: Side}{I α β γ G:Type}[LinearOrder I][Fintype I][Fintype α][Fintype β][Fintype γ]
-- old bank
namespace ShoreQ
open Hest XGarden Ladder3 Branch Urn Tenant Nacre Drapes Salt Sour.SliceRoof Rill Rill.CreekX Broc Thera Jet CF.Forge
variable {R:Loom n}{k:ℕ}{t d a c b v:ℝ}{F:Elm n Unit d a c} {Q:BudgetPoint}
attribute [local instance] boreKSpace boreXN
local notation "S0"=> Support (More n)
local notation "SA"=> Seat n
-- Earn body gear.P2. require late clock.
structure Hann (P:BudgetPoint)(k:ℕ)(t:ℝ):Prop where
    pitch:P.threshold≤t
    rent :cipherK k ≤ 5*P.B
    crane :3 ≤ P.B
    canon :P.order = 6
variable (u:Roof n t d k R) (q:0<d)(y:hud_T 7 b)(b':0≤v)(e:coinH b v)(p:Hann Q k t)(h:ℝ)(vh:1≤h)
local notation "Xρ"=> uplift F R k
local notation "Ωr"=> releaseQ F
variable (V X D:Support (More n))
abbrev MealD (F:Elm n Unit d a c)(R:Loom n)(k:ℕ) (t:ℝ): LeaseQ (Support (More n)) n:=⟨id,fun i=> Lattice.halo (k+22) i, fun i D x=> boat (uplift F R k D i t x),fun i x=>boat (releaseQ F i (R x))⟩
local notation "Xf"=> MealD F R k t
private lemma ΛV (F:Op (Single n))(w:∀ i j,F i j ≠0 → aptK i∈ V ∧ aptK j∈ V): Flour (camp V) (boat F).val :=by
 let A:FC (Dwell n):= faceD true false F; change Flour _ A; unfold A faceD twinD
 apply Flour.sum; intro i _; apply Flour.sum; intro j _; by_cases p:F i j=0; · rw[p,zero_smul]; exact Flour.trivial
 obtain ⟨x,z⟩:=w i j p; let I:= put (n:= Dwell n) (true,i); let J:= put (n:=Dwell n) (false,j)
 apply Flour.smul; change Flour _ (I*J); let E:Dwell n:= (true,i); let B:Dwell n:= (false,j); have hI:E∈camp V:= mem_filter.mpr ⟨mem_univ _,x⟩; have hJ:B∈ camp V:=mem_filter.mpr ⟨mem_univ _,z⟩
 rw [show I=poke {E} from (Poly.tag_once (Pastry.cane (Dwell n)) E).symm, show J=poke {B} from (Poly.tag_once (Pastry.cane (Dwell n)) B).symm, Poly.tag_mul, if_pos (show Disjoint ({E}:Finset (Dwell n)) {B} from (by simp[E,B]))]; apply Flour.smul; apply Flour.point; refine mem_filter.mpr ⟨mem_powerset.mpr (union_subset (singleton_subset_iff.mpr hI) (singleton_subset_iff.mpr hJ)),?_⟩; simp [E,B,Wheat]
local notation "Ft"=> uplift F R k D V t
include u q
lemma V_apt (x:Orbit n) : Flour (camp V) ((Xf).raw V x).val :=by
 apply ΛV
 intro i j p; let X:=F.coat V|>.1 (); rw[re_L _ _ _ (u.paid _) q] at p; have h:F.W V i j ≠0:= ne_of_gt (lt_of_lt_of_le (norm_pos_iff.mpr p) ((X.expo i j).bounded _))
 exact ((X.expo i j).triggered h).2
lemma V_lit (x:Orbit n): Flour (camp V) ((Xf).issue V D x).val:=by
 change Flour _ (boat (Ft x)).val; unfold Sour.SliceRoof.uplift; split; exact V_apt (F:=F) u q V x
 change Flour _ (faceD true false (0:Op (Single n))); unfold faceD twinD; simp only [Matrix.zero_apply,zero_smul,sum_const_zero]; exact Flour.trivial
variable (tL:Lattice.halo (k+22) V⊆ X)(pL:Lattice.halo (cipherK k) D⊆ X)
include tL pL
lemma V_Θ : ThemeR X ((MealD F R k t).issue V D):=by
 let f:= (Xf).issue V D
 have ht(x): (f x).val=faceD true false (Ft x):=rfl
 have hx: Measurable f:=by
    have hs:Measurable (Ft):=lift_meter (F:=F) u q -- tune
    have hp: Measurable fun x:Orbit n=> (f x).val:=by
      simp_rw [ht]; unfold faceD twinD; apply Finset.measurable_fun_sum; intro i _; apply Finset.measurable_fun_sum; intro j _
      have hg : Measurable (fun x:Orbit n=>(Ft x) i j):= by
        have hb :Continuous (fun x:Op (Single n)=> x i j):= (continuous_apply j).comp (continuous_apply i)
        letI:MeasurableSpace (Op (Single n)):=borel _
        haveI:BorelSpace (Op (Single n)):=⟨rfl⟩
        exact hb.measurable.comp hs
      exact hg.smul_const _
    change @Measurable _ (Cipher n) _ (borel _) _; have he:@Measurable _ (Cipher n) _ Subtype.instMeasurableSpace f:=hp.subtype_mk; rw [@BorelSpace.measurable_eq (Cipher n) _ Subtype.instMeasurableSpace (Subtype.borelSpace _)] at he; exact he
 refine ⟨fun i j a t=> congrArg boat (lift_eq (F:=F) u pL tL q a t),fun i=> ((V_lit (F:=F) u q V D i).lift (camp_b ((Lattice.halo_subset _ _).trans tL))),hx,fun i j=>?_⟩
 change boat _= _; rw[show uplift F R k D V t (Lattice.gauge j i.1, threadG j i.2)= twist (tradew n j) (Ft i) from lift_gZ u q _]; exact Eq.symm (Hest.sailR false false _ _)
include vh
lemma V_M {Zc:Single n→ Single n→ℝ}(p:0≤Zc)(hx:∀ (x:Lime Q X D)(i j: Single n),Pence Q.order (fun y=>uplift F R k D V t (citrus Q X D x y) i j) 0 (Zc i j)): Medal Q X D ((MealD F R k t).issue V D) h ((∑ i:Single n,∑ j,Zc i j)*h^2):=by
 let f:= fun x:Orbit n=> ((Xf).issue V D x).val; have ht:OpTheme X f false:=opThemeHold _ (V_Θ (F:=F) u q V X D tL pL)
 let L(i j:Single n)(u:Orbit n):= (Ft u) i j; let g(i j:Single n)(u:Orbit n):= L i j u • (wire true i* wire false j)
 have he: f=∑ i:Single n,∑ j,g i j:=funext fun i=>by simp only [Finset.sum_apply]; rfl
 have hm(i j:Single n): Portμ (citrus Q X D) 0 (g i j) h (Zc i j*h^2) Q.order:=by
    rw [pow_two]; change Portμ _ _ (g i j) _ _ _; exact ((mist_p Q.order (citrus Q X D) h 0 (true,i) vh).mult (mist_p _ _ _ (0:tangD n) (false,j) vh) (zero_le_one.trans vh)).scale _ (p i j) (fun a=>hx a i j)
 have hM: Portμ (citrus Q X D) 0 f h ((∑ i:Single n,∑ j,Zc i j)*h^2) Q.order:=by rw [he]; simp_rw [sum_mul]; exact Portμ.sum _ _ _ fun i _=>Portμ.sum _ _ _ fun j _=>hm i j
 rw [show ((MealD F R k t).issue V D)=(fun i=> fair (f i)) from ?_]; exact fair_port Q X D f hM ht
 funext i; apply Subtype.ext; rw[pie_s _ X (ht.lit i)]; exact (fineShape _).allP
include y b' e p
abbrev BudgetValve (v d:ℝ):= 7 * (DeskK v d + 1)
abbrev book_S (d a c v:ℝ)(F:Elm n Unit d a c)(h:ℝ)(V:Support (More n)):= BudgetValve v d*(ζΧ d a c F V)*h^2
lemma V_base:Medal Q X D ((MealD F R k t).issue V D) h (book_S d a c v F h V):=by
 let L:= DeskK v d; have hl:0≤L:=by unfold L DeskK composeCost; positivity
 let c₀:=BudgetValve v d; let Λ(i j:Single n):= c₀*Wloop F V i j
 unfold book_S ζΧ; simp_rw[mul_sum]; apply V_M (F:=F) u q h vh V X D tL pL (Zc:=Λ) -- tune
 · exact fun i j=> mul_nonneg (by unfold c₀ BudgetValve; positivity) (loop_p ..)
 intro x i j; have H:= (stern_bill (F:=F) u p.pitch pL tL q x.property.2 p.rent p.crane y e b' i j x.property.1).1
 apply Pence.mono (Rue.bare_p _ _ (H.order (show Q.order≤7 from (by rw[p.canon]; omega))))
 unfold Λ c₀ BudgetValve; rw[p.canon]; norm_num; apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (expandW ..) hl) (by norm_num:0≤ (7:ℝ))).trans
 nlinarith only [loop_p (F:=F) (S:=V) i j]
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end
