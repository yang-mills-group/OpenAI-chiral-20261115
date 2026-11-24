import YM.CF.BProof.Garden.Fruit
import YM.CF.BProof.Oasis.Arrow
/-! Ordinary vertices, regular vs force. Only actual camps. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Oasis
open Function Filter Fock Finset NormedSpace Garden Align Wick Double Pastry Crystal MeasureTheory
open Lattice Tenant Lat Cube Tulip Scree Skye
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {N:Side}
abbrev Starry (I:Type)[Fintype I][LinearOrder I](s:Finset I):= (Wheat s).erase ∅
lemma decomposeW{I:Type}[Fintype I][LinearOrder I](S:Finset I)(x:Dough I)(g:Flour S x.val)(v:ℝ)(E:Type)[Fintype E] -- tune args remove
 (f: ↑(Starry I S)→ Dough I)(e:∀ i, (f i).val=poke i.val): v • x=hollow (v • pane x)+ ∑ i:Starry I S, hollow (v • crumb x.val i.val)* f i:=by
 apply Subtype.ext; change v • x.val = (v • pane x) • (1:FC I)+(Dough I).val _; rw [map_sum]; nth_rw 1 [g.pin]; rw [← add_sum_erase (Wheat S) _ (by simp [Wheat]: (∅:Finset I)∈ Wheat S), smul_add, smul_sum]; congr 1; · rw [smul_assoc,show poke (∅:Finset I)=1 from Poly.tag_void _]; rfl
 rw [← Finset.sum_attach ((Wheat S).erase ∅)]; apply sum_congr rfl; intro i _; rw [show (Dough I).val (hollow _*f i)= (v • crumb x.val i.val) • (f i).val from hollow_face .., e,smul_assoc]
abbrev Stem(N:Side):= Bool × Hub N -- true slip
abbrev StarR (i:Stem N):= ↥(Starry (Dwell N) (Scree.camp i.2.val.2))
abbrev OptionR(N:Side):= Sigma (@StarR N)
abbrev OriginR(i: Stem N): Seat N := i.2.val.1
abbrev PartyF(i:Force N) := ↥(Wheat (Scree.camp i.val.1.val.2))
abbrev OptionF(N:Side):= Sigma (@PartyF N)
def bkiln{I:Type}[LinearOrder I](S:Finset I):= S.sort (· ≤ ·)
lemma bkiln_f{I:Type}[LinearOrder I](S:Finset I):(bkiln S).Nodup:=sort_nodup ..
lemma bkiln_size{I:Type}[LinearOrder I](S:Finset I):(bkiln S).length=S.card:=length_sort ..
lemma bkiln_k{I:Type}[LinearOrder I](S:Finset I):(bkiln S).toFinset=S:=by simp [bkiln]
def lineR (N:Side): Dew (OptionR N) (Dwell N) where
 free:=fun _ _=>True
 line v:=bkiln v.2.val
 fresh v:=bkiln_f ..
 even v:=by rw [bkiln_size]; exact (mem_filter.mp (mem_of_mem_erase v.2.property)).2
def lineF (N:Side): Dew (OptionF N) (Dwell N) where
 free i j:=i.1 ≠ j.1 ∧ Disjoint i.1.val.1.val.2 j.1.val.1.val.2
 line v:=bkiln v.2.val
 fresh v:= bkiln_f ..
 even v:=by rw [bkiln_size]; exact (mem_filter.mp v.2.property).2
lemma graceR(i:OptionR N) : ((lineR N).grace i).val=poke i.2.val:=rfl
lemma graceF(i:OptionF N) : ((lineF N).grace i).val=poke i.2.val:=rfl
variable (D:GramM N)
def readR(i:Stem N)(x:Pane N):= numbE D.p.threshold i.2.val.2 ((if i.1 then D.slip else D.F) i.2) x
def foldR(v:ℝ)(x:Pane N):= v • (∑ i:Stem N, readR D i x)
lemma fold_one(x:Orbit N): foldR D 1 x.1=whole D x:=by unfold foldR whole; rw [one_smul,Fintype.sum_prod_type,Fintype.sum_bool]; simp only [readR,ite_true,Bool.false_eq_true,ite_false]; exact add_comm .. -- tune order
lemma fold_smr(v:ℝ)(x:Orbit N): foldR D v x.1=v • whole D x:=by rw [←fold_one,foldR,foldR,one_smul]
structure Fitted (D:GramM N) : Prop where
 press (i:Stem N)(x:Pane N): Flour (Scree.camp i.2.val.2) (readR D i x).val
 force (i:Force N)(x:Orbit N): Flour (Scree.camp i.val.1.val.2) (Scree.clamp D.p i (D.K i) x).val

abbrev DecR (v:ℝ)(x:Pane N)(i:Stem N):ℂ := v • pane (readR D i x) -- tune SCALAR parity under real scal
abbrev PriceR (v:ℝ)(x:Pane N) :ℂ:= ∑ i:Stem N, DecR D v x i
lemma hollowMass {I:Type*}[Fintype I][LinearOrder I]{E:Type*}[Fintype E](f:E→ℂ): hollow (n:=I) (∑ i,f i)=∑ i,hollow (n:=I) (f i):=Subtype.ext (by change (∑ i,f i) • (1:FC I)=(Dough I).val _; rw [Finset.sum_smul,map_sum]; rfl)
def FeeR(v:ℝ)(x:Pane N)(i:OptionR N):ℂ:= v • crumb (readR D i.1 x).val i.2.val
def RateF(f:Pollen (Site (More N)))(x: Orbit N)(i:OptionF N):ℂ:=style i.1.val.2 f * crumb (Scree.clamp D.p i.1 (D.K i.1) x).val i.2.val
-- mark scalar in Fgas uses *sum* across budgets even slip
lemma fare(x:Pane N)(z:Fitted D)(v:ℝ): foldR D v x=hollow (PriceR D v x)+ ∑ i:OptionR N,(lineR N).orts (FeeR D v x) i:=by
 unfold foldR PriceR OptionR; rw [smul_sum, Fintype.sum_sigma, hollowMass,←sum_add_distrib]; apply sum_congr rfl; intro i _; exact decomposeW _ _ (z.press i x) _ Unit (fun j=>(lineR N).grace ⟨i,j⟩) (fun j=>graceR _) -- tune
lemma recovered(v:ℝ)(z:Fitted D)(x:Pane N) : exp (foldR D v x)= exp (hollow (PriceR D v x))* ((lineR N).foldS (FeeR D v x)):=by
 letI : NormedAlgebra ℚ (Cipher N) := NormedAlgebra.restrictScalars ℚ ℝ _; rw [fare D x z,exp_add,(lineR N).eTerm _ (fun _ _=>trivial)]; intro i h; apply (mem_erase.mp i.2.property).1; rw [←show (((lineR N).line i).toFinset)=i.2.val from ?_ ,h,List.toFinset_nil]; simp only [lineR,bkiln_k]
lemma readers(f:Pollen (Site (More N)))(z:Fitted D)(x:Orbit N): red D x f= (lineF N).foldS (RateF D f x):=by
 have hp(i:Force N): aster D x f i=∑ j:PartyF i,(lineF N).orts (RateF D f x) ⟨i,j⟩:=by
    let S:=Scree.camp i.val.1.val.2; let Z:=Scree.clamp D.p i (D.K i) x; let v:= style i.val.2 f; have he: Z=∑ j:PartyF i,hollow (crumb Z.val j.val) * (lineF N).grace ⟨i,j⟩:=by
       apply Subtype.ext; change Z.val=(Dough _).val _; rw [map_sum]; have ht(i:PartyF i):(Dough _).val (hollow (crumb Z.val i.val) * (lineF N).grace ⟨_,i⟩)=crumb Z.val i.val • poke i.val:=hollow_face ..; simp_rw [ht]; exact (by nth_rw 1 [(z.force i x).pin]; rw [← Finset.sum_attach]; rfl)
    change hollow v * Z=_; nth_rw 1 [he]; rw [mul_sum]; apply sum_congr rfl; intro j _; rw [Dew.orts,RateF,←Dew.hollowM, mul_assoc]
 unfold red; rw [(lineF N).choiceP (u:=fun i j:Force N=>Disjoint i.val.1.val.2 j.val.1.val.2) rfl]; simp_rw [hp]; rfl
end YM.CF.BProof.Oasis
