import GaugeFieldConstruction.HopeQ
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 55000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief
open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
namespace Pitching
open Vow Bake Larch
namespace Focus
open Neon
open Mew Vow Rive Roots
open scoped YM.CF.Mew
namespace CoeffArc
section
open TableF Lenten Lenten.Layout Fren
open Frugal
open Py.Riant
-- arbitrary finite labels grouped by Seat. further partition within group by programs.D.
structure Directory (I S:Type) where
    own : I → S
    kind : I → Bool
    depth : S → ℕ
variable {N:Side}{I S:Type}[LinearOrder I][Fintype I][Fintype S][DecidableEq S]
namespace Directory
variable (P:Directory I S)
abbrev NameK (s:S)(d:Bool) := {i:I // P.own i=s∧ P.kind i=d}
abbrev Pname (s:S) := NameK P s true
abbrev Vname (s:S) := NameK P s false
-- confirm typeclass p
abbrev TourG := ∀ s:S,P.Pname s  → ℕ
abbrev TourF :=∀ s:S,P.Pname s  →  Waves
abbrev InShape (v:TourF P) (V:TourG P)(τ:ℝ):Prop:=∀ s:S, Planaris (V s) ΓProj (P.depth s) (v s) τ
abbrev F_v (o:S → Seat N):=fun i:I=> o (P.own i)
lemma clan_y (o:S → Seat N)(s:S)(b:Bool)(i: NameK P s b): F_v P o i.val=o s:=congrArg o i.property.1
lemma clan_X (o:S → Seat N)(s:S)(b:Bool)(i:NameK P s b):pipe_ζ (F_v P o) i.val=univ.filter fun j:I=> F_v P o j=o s:=by unfold pipe_ζ; rw [clan_y]
abbrev QSign (p:BudgetPoint)(M:Tulip.Male)(o:S →  Seat N)(F:I → RegBudget N)(L:Side)(h b q:ℝ)(V:TourF P):Prop:=∀ i:S,(∀ x:Pname P i, TollsK p (o i) M (F x.val) L q h b (P.depth i) (V i x)) ∧∀ x:Vname P i,TollsK p (o i) M (F x.val) L q h b (P.depth i) 0
abbrev ToPC := ∀ s:S, FrameK (Pname P s) →ₗ[ℂ] FrameK (Pname P s)
abbrev ToMG := ∀ s:S,Vname P s →  FrameK (Pname P s)
abbrev DayP (K: ToPC P) (L:Side)(V:TourG P)(i:S)(v:Pname P i)(b:I):ℂ:= if h:P.own b=i ∧ P.kind b=true then PickS (K i) v L (V i) ⟨b,h⟩ else 0
abbrev DayF (J:ToMG P)(K: ToPC P) (L:Side)(V:TourG P)(i:S)(v:Vname P i)(b:I):ℂ:= let z:= (GapGain L (P.depth i):ℂ); (if h:P.own b=i ∧P.kind b=true then z*(PrizeP (J i) (K i) v L (V i) ⟨b,h⟩) else 0)+if b=v.val then z else 0
abbrev Ctags (J:ToMG P)(K: ToPC P)(L:Side)(V:TourG P):I →  I → ℂ:=fun b i=> if h:P.kind i=true then DayP P K L V (P.own i) ⟨i,rfl,h⟩ b else DayF P J K L V (P.own i) ⟨i,rfl,(Bool.eq_false_iff.mpr h)⟩ b -- bool lem
variable (o:S →  Seat N)(J:ToMG P)(K: ToPC P)(L:Side)(V:TourG P)
abbrev MatchRow (X:I → Zone N)(C:I →  I → ℂ)(j:I):Zone N:=∑ i∈ pipe_ζ (F_v P o) j,C i j • X i
lemma Day_C (s:S)(v:Pname P s)(b:I): P.Ctags J K L V b v.val=DayP P K L V s v b:=by
 rcases v with ⟨x,h,e⟩; subst s; exact dif_pos e
lemma Day_G (s:S)(v:Vname P s)(b:I): P.Ctags J K L V b v.val=DayF P J K L V s v b:=by
 rcases v with ⟨x,h,e⟩; subst s; exact dif_neg (show ¬P.kind x=true from (by simp [e]))
-- convert sums via subtypes, without proof irrelevance clutter.
lemma shift_p {A:Type*}[AddCommMonoid A](v:I)(s:S)(b:Bool)(p:P.own v=s)(F:I →  A)(H:P.NameK s b → A)(h:∀ i,P.own i≠s ∨ P.kind i≠b  →  F i=0)(t:∀ i:P.NameK s b,F i.val=H i): ∑ i∈pipe_ζ (P.F_v o) v,F i=∑ i:P.NameK s b,H i:=by
 let V:Finset I:= univ.image (Subtype.val:P.NameK s b →  I); have he:V ⊆ pipe_ζ (P.F_v o) v:=by rintro x w; obtain ⟨i,l,rfl⟩:=mem_image.mp w; exact mem_filter.mpr ⟨mem_univ _,(clan_y ..).trans (congrArg o p).symm⟩
 rw [← sum_subset he _]; · unfold V; rw [sum_image (fun _ _ _ _ h=> Subtype.ext h)]; exact sum_congr rfl (fun i _=>t i)
 intro i v e; by_cases w:P.own i=s∧P.kind i=b
 · exact False.elim (e (mem_image.mpr ⟨⟨i,w⟩,mem_univ _,rfl⟩))
 exact h i (not_and_or.mp w) -- tune
variable (X:I →  Oath.Zone N)(s:S)
lemma Tip_C (v:P.Pname s) : P.MatchRow o X (P.Ctags J K L V) v.val=W_s (fun i:P.Pname s=>X i.val) (PickS (K s) v L (V s)):=by
 refine shift_p P o v.val s true v.property.1 _ _ ?_ ?_
 · intro i t; rw [Day_C]; have hq:¬(P.own i=s∧P.kind i=true):=not_and_or.mpr t; rw [DayP,dif_neg hq,zero_smul]
 intro i; rw [Day_C]; unfold DayP; rw [dif_pos i.property]
lemma Tip_gap (v:P.Vname s) : P.MatchRow o X (P.Ctags J K L V) v.val= PrizeZ (PrizeP (J s) (K s) v L (V s)) (X v.val) (fun i:P.Pname s=>X i.val) (P.depth s) L:=by
 let Y(i:P.Pname s):= X i.val; let T:=v.val; let C:= (GapGain L (P.depth s):ℂ); let Φ:=PrizeP (J s) (K s) v L (V s); let B(i:I):ℂ:= if h:P.own i=s∧P.kind i=true then C*(Φ ⟨i,h⟩) else 0; unfold MatchRow; let D:= pipe_ζ (P.F_v o) v.val
 have hv(i:I):Ctags P J K L V i v.val=B i + if i=v.val then C else 0:=Day_G ..
 simp_rw [hv,add_smul, sum_add_distrib]; unfold PrizeZ; change ∑ i∈D,B i • X i + (∑ i∈D,(if i=v.val then C else 0) • X i)= C • _; rw [smul_add,add_comm (C • _)] -- ite_sum unknown replace
 refine congrArg₂ (·+·) ?_ ?_
 · unfold W_s; rw [Finset.smul_sum]; refine shift_p P o v.val s true v.property.1 _ _ ?_ ?_
   · intro i t; unfold B; rw [dif_neg (not_and_or.mpr t), zero_smul]
   intro i; unfold B; rw [dif_pos i.property]; exact mul_smul ..
 rw [sum_eq_single_of_mem (s:=D) v.val (mem_filter.mpr ⟨mem_univ _,rfl⟩)]; simp; intro i h v; rw [if_neg v,zero_smul]
-- ℓ1 choices Column.L uniform.D post via simple cap maxima.
abbrev PostP (L:Side)(D:ℕ):ℝ:= (Rateκ L D)⁻¹*κMini L
abbrev PostQ (L:Side)(D:ℕ):ℝ:=GapGain L D*(LαK L (-1+3*Alto))+GapGain L D
abbrev ψMax (L:Side)(n:ℕ):= |PostP L n| +|PostQ L n|
abbrev Maxi (L:Side):= 1+∑ i∈range 3, ψMax L i
variable (H:∀ i,P.depth i ≤2)
include H
lemma Column_C (v:P.Pname s)(hK:LoomK (PickS (K s) v L (V s)) ≤ PostP L (P.depth s)): ∑ i∈pipe_ζ (P.F_v o) v.val,‖P.Ctags J K L V i v.val‖ ≤ Maxi L:=by
 have he:=hK.trans (le_abs_self _); refine le_trans (le_trans (le_of_eq ?_) he) ?_
 · refine shift_p P o v.val s true v.property.1 _ _ ?_ ?_
   · intro i t; rw [Day_C,DayP,dif_neg (not_and_or.mpr t),norm_zero]
   intro i; rw [Day_C,DayP,dif_pos i.property]
 apply le_trans (b:=ψMax L (P.depth s)) (le_add_of_nonneg_right (abs_nonneg _)); refine (single_le_sum (f:=ψMax L) (fun i u=>add_nonneg (abs_nonneg _) (abs_nonneg _)) (mem_range.mpr (Nat.lt_succ_of_le (H s)))).trans (le_add_of_nonneg_left zero_le_one) -- tune ψMax
lemma Column_G (v:P.Vname s)(hK: LoomK (PrizeP (J s) (K s) v L (V s)) ≤ LαK L (-1+3*Alto)): ∑ i∈pipe_ζ (P.F_v o) v.val,‖P.Ctags J K L V i v.val‖ ≤ Maxi L:=by
 let C:= (GapGain L (P.depth s):ℂ); let Φ:= PrizeP (J s) (K s) v L (V s); let F(i:I):ℂ:= if h:P.own i=s∧P.kind i=true then C*(Φ ⟨i,h⟩) else 0; let Q:=pipe_ζ (P.F_v o) v.val;
 have he(i:I):Ctags P J K L V i v.val= F i+if i=v.val then C else 0:=Day_G ..
 change ∑ i∈Q,_≤_; simp_rw [he]; apply le_trans (sum_le_sum (g:=fun i=>‖F i‖+‖if i=v.val then C else 0‖) (fun i _=>norm_add_le ..)); rw [sum_add_distrib,sum_eq_single_of_mem (s:=Q) (f:=fun i=>‖if i=v.val then C else 0‖) v.val (mem_filter.mpr ⟨mem_univ _,rfl⟩),if_pos rfl]; swap; · intro i h u; rw [if_neg u,norm_zero]
 have hf:∑ i∈Q,‖F i‖= ‖C‖*LoomK Φ:=by
    unfold LoomK; rw [mul_sum]; refine shift_p P o v.val s true v.property.1 _ _ ?_ ?_
    · intro i t; unfold F; rw [dif_neg (not_and_or.mpr t),norm_zero]
    intro i; unfold F; rw [dif_pos i.property, norm_mul]; -- rfl tune
 have hp:‖C‖=GapGain L (P.depth s):=α_money _ (Gap_nv ..)
 rw [hf]; refine le_trans (b:=PostQ L (P.depth s)) ?_ ?_; rotate_left
 · apply le_trans (b:=ψMax L (P.depth s)) ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))); exact (single_le_sum (f:=ψMax L) (fun i u=> add_nonneg (abs_nonneg _) (abs_nonneg _)) (mem_range.mpr (Nat.lt_succ_of_le (H s)))).trans (le_add_of_nonneg_left zero_le_one)
 unfold PostQ; rw [←hp]; exact add_le_add_left (mul_le_mul_of_nonneg_left hK (norm_nonneg _)) _ -- goal order
end Directory
end
end CoeffArc
end Focus
end Pitching
end YM.CF.Py.Rate
end
