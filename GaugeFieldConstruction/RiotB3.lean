import GaugeFieldConstruction.Polter3
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
open Ladder3 Salt Levier Thera Urn Hest Sault Pastry Haro
open XGarden XGarden.MastTin SeasonH Branch Tenant Drapes Rill Nacre Broc SliceRoof
open XGarden.Shield
open Leaf
open Wosk XGarden.MastTin.MintB
attribute [local instance] boreKSpace boreXN opCStarAlgebra
variable {R:Loom n}{k:ℕ}{t d a c e r h:ℝ} 
variable (F:Elm n Unit d a c)(R:Loom n)(k:ℕ)(t:ℝ)
-- halves option. Cell width one.V orientation motion.
variable (X S D:Support (More n))(W:Orbit n)
local notation "Vx"=> uplift F R k D S t
local notation "Y"=> Single n
local notation "G"=> LeanV (Single n)
variable (u:Roof n t d k R)(q:0<d)
variable (o:Seat n) (Z:Paper n)(M:Male) (j:ℕ)
local notation "V0"=> pack3 k o
local notation "Zd"=> Pach o
section pals
local notation "H"=> fun S=>rawH F R S W
local notation "Y0"=> Dial.spar j M (R W)
variable (A:NearL F (fun _=>hemi_L n j M))
include u q A
lemma γSale (i i':LeanV (Single n)): ∑ S:Support (More n), rawH F R S W i i'= rayP (Y0) i i':=by
    have ht:= u.paid W
    let P:= Y0; let D(S:Support (More n)):= releaseQ F S (R W); let B:=halfBand n
    have he: ∑ i:Support (More n),D i=P-B:=by unfold D; simp_rw[re_L _ _ _ ht q]; exact (A () _ _ ht rfl).symm -- rhs choose light
    have hy: ∑ i:Support (More n),sip0 i = B:=by
       ext a b; rw[Matrix.sum_apply, sum_eq_single ({aptK a}:Support (More n))]; rw[sip_e]; unfold B halfBand; by_cases p:a=b <;> simp [p,Matrix.one_apply,div_eq_mul_inv] -- tune
       intro i _ h; rw [sip_e]; exact if_neg (fun k=> h k.1)
       simp
    have hp:P=P:=rfl
    obtain ⟨f,x⟩:=i; obtain ⟨g,y⟩:=i'; cases f<;>cases g
    · exact sum_eq_zero fun _ _=>rfl
    · change (∑ i',(sip0 i'-D i') x y) = _; rw[← Matrix.sum_apply (g:=fun i'=> sip0 i'- D i'),sum_sub_distrib,hy,he]; change _=(1-P) x y; rw [show B-(P-B)=1-P from (by unfold B halfBand; module)]
      -- B.len1.Prox
    · change (∑ i',(sip0 i'+ D i') y x) =_; rw[←Matrix.sum_apply (g:=fun i'=>sip0 i'+D i'),sum_add_distrib,he,hy]; change _=P y x; rw [add_comm,sub_add_cancel]
    exact sum_eq_zero fun _ _=>rfl
lemma popStack (a:LeanV (Single n)): ∑ p:SP3 n, pinMode (fun S=>rawH F R S W) p a= Icycle (rayP (Dial.spar j M (R W))) a:=by
 rw [Fintype.sum_option]; change put a + (∑ h:Support (More n),iceK (fun i j=> rawH F R h W i j) a)= put a+_
 apply congrArg; unfold iceK; simp_rw[←γSale F R k t W u q M j A,Finset.sum_smul]; exact Finset.sum_comm -- tune orientation binder order
lemma castStack (x:Wa n): ∑ i:L3 n, tokenMode (fun S=>rawH F R S W) i x= logL (Icycle (rayP (Y0))) (veilD x):=by
 rcases x with _|⟨k,i,j'⟩
 · rw [sum_eq_single ((none,none):L3 n)]; exact rfl; intro i _ p; apply if_neg; intro h; unfold τPure at h; exact p (Prod.ext (Option.isNone_iff_eq_none.mp (Bool.and_eq_true ..|>.mp h).1) (Option.isNone_iff_eq_none.mp (Bool.and_eq_true ..|>.mp h).2))
   simp
 unfold L3; rw [Fintype.sum_prod_type]; let G0(S:Support (More n)):=rawH F R S W; let x:LeanV (Single n):= (k,i); let y:LeanV (Single n):= (!k,j'); let X:= Icycle (rayP (Y0)); change (∑ a:SP3 n,∑ b:SP3 n,pinMode G0 a x*pinMode G0 b y) = X x*X y
 simp_rw [←mul_sum,←Finset.sum_mul]; rw[show ∑ a:SP3 n,pinMode G0 a x=X x from popStack F R _ _ W u q M j A x,show ∑ a:SP3 n,pinMode G0 a y=X y from popStack F R _ _ W u q M j A y] -- tune args
variable (D:ChartP n)(p₁:∀ i:Wa n,D i≠0→ DomainP (Pach o) i)
omit A
include p₁
lemma ivory_white (i:L3 n)(t:¬warmMode o i): wax D i (fun S=>rawH F R S W)=0:=by
 apply sum_eq_zero; intro i' g; by_cases h:D i'=0; · rw [h,zero_smul]
 have hp:=p₁ _ h; suffices ht: tokenMode (fun S=>rawH F R S W) i i'=0 by rw[ht,smul_zero]
 rcases i' with _|⟨b,k,j⟩
 · apply if_neg; intro p; let a:=none (α:=Support (More n)); have hu:i=(a,a):=Prod.ext (Option.isNone_iff_eq_none.mp ((Bool.and_eq_true _ _).mp p).1) (Option.isNone_iff_eq_none.mp ((Bool.and_eq_true _ _).mp p).2); exact t (hu ▸ ⟨True.intro, True.intro⟩)
 have he(i:SP3 n)(t':¬ imply3 o i)(j:LeanV (Single n))(p:aptK j.2∈ Pach o):pinMode (fun S=>rawH F R S W) i j=0:=by
    obtain (_|L):=i; exact False.elim (t' True.intro) -- tune. $none$
    exact sum_eq_zero (fun i _=> by
       have px:rawH F R L W j i=0:=Classical.byContradiction (fun t=> (t' (show ¬Disjoint Zd L from (fun y=> Finset.disjoint_left.mp y p ((Finset.mem_filter.mp (raw_i F R _ _ L W u q j i t).1).2)))))
       dsimp only; rw [px,zero_smul])
 unfold warmMode at t; change _*_= _; by_cases t':imply3 o i.1; · exact mul_eq_zero_of_right _ (he _ (fun u=>t ⟨t',u⟩) (!b,j) hp.2)
 exact mul_eq_zero_of_left (he _ t' (b,k) hp.1) _
include A
variable (P:BudgetPoint)
lemma apex_read (X:Paper n)(L:αLines X W.1=D)(u:pingS P.threshold (Pach o) W.1): ∑ i:L3 n,(ArchQ F R k t P o i X).raw W=∑ i:Wa n, D i • logL (Icycle (rayP (Dial.spar j M (R W)))) (veilD i):=by
    have hp(i): (ArchQ F R k t P o i X).raw W=wax D i (fun S=>rawH F R S W):=by
       by_cases h:warmMode o i; exact (if_pos ⟨u,h⟩).trans (congrArg (fun d=>wax d _ _) L)
       exact (if_neg (fun x=>h x.2)).trans (ivory_white F R k t W ‹Roof _ _ _ _ _› q o D p₁ i h).symm
    simp_rw[hp]; unfold wax; rw [sum_comm]; apply sum_congr rfl; intro i _; rw [← Finset.smul_sum]; exact congrArg (D i • ·) (castStack F R k t W ‹_› q M j A i)
#print axioms apex_read
end pals
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end
