import GaugeFieldConstruction.CinderQ3
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
variable {S:α→Support (More n)} (V:Mica I β n)
structure Tuner (I:Type)(S:α→Support (More n)) where
    anchor: Hub n
    d : ℕ
    bound_d:d≤2
    from_ : Heart anchor S d→List I
    issue (x:Heart anchor S d): Support (More n)→Support (More n)→ Orbit n→FC (Dwell n)
namespace Tuner
open Mica
variable (L:Tuner I S)(T:Ids n) (σ:I→Seat n)
local notation "Ψ"=> Heart L.anchor S L.d
local notation "R0"=> Legist L.anchor S L.d
local notation "Vx" y:max=> ((R0) y).val.2
local notation "Xd" y:max b:max=> (mixedHub (R0 y) V.z b).val.2
local notation "Dh"=> til V.z
abbrev rockT (x:Heart L.anchor S L.d): Copy n:=fun u=> fair (L.issue x (Vx x) ∅ u)
def pureT : Grotto I S V.z:=⟨L.anchor,L.d,L.bound_d,false,L.from_,fun x i=> L.rockT x (i,T), (fun x _=> L.from_ x),(fun _ _=> 0)⟩ -- missing flag!
noncomputable def fillT (x:Heart L.anchor S L.d)(Y:Finset β): Copy n:=
 let P:= Legist L.anchor S L.d x; let X:=(mixedHub P V.z Y).val.2; let D:=til V.z Y; let F:=∏ i∈Y,V.K i
 (fun z=> fair (L.issue x X D z* (F z).val))-(if Disjoint P.val.2 D then (L.rockT x)*F else 0)
def busyT : Grotto I S V.z:=⟨L.anchor,L.d,L.bound_d,true,L.from_,fun _=>0,(fun x P=>L.from_ x ++ V.legend P),L.fillT V⟩
variable {P:BudgetPoint}{r h c:ℝ}{K:ℕ}
structure accords (P:BudgetPoint)(σ:I→Seat n)(r h c:ℝ)(K:ℕ)(g:α→ℝ) :Prop where
    core(y:Heart L.anchor S L.d)(X D:Support (More n))(p:(Legist L.anchor S L.d y).val.2⊆ X)(w:Lattice.halo K D⊆ X): OpTheme X (L.issue y X D) false ∧ Portμ (citrus P X D) 0 (L.issue y X D) h (Bplain (L.from_ y).length (c*(∏ j:Fin L.d,g (y.val j))) r) P.order ∧(L.issue y X D≠0 → ∀ j,j∈L.from_ y → σ j∈X) -- tune linter. IView
    tag(x:Heart L.anchor S L.d)(V:Orbit n)(T:Ids n): L.issue x (Legist L.anchor S L.d x).val.2 ∅ (V.1,T) = L.issue x (Legist L.anchor S L.d x).val.2 ∅ V
-- Support at D depends on K, only for real. Want raw equality of expects every valid.F.Truth separate. Later.Compar Guru at injective. 
section
variable {g:α→ℝ} {w:β→ℝ} (a:Tuner.accords L P σ r h c K g)(q: Mica.MintH V σ P h r K w)(p:1≤h)(u:0<r)(t:0≤g)(l:0≤c)(y:0≤w)
local notation "aΓ" x:max=> (c*(∏ j:Fin L.d,g ((x:Ψ).val j)))
include a
lemma primal (x:Heart L.anchor S L.d): Medal P (Vx x) ∅ (L.rockT x) h (Bplain (L.from_ x).length (aΓ x) r) ∧ (L.rockT x≠0 → poke_F σ (Vx x) (L.from_ x).toFinset):=by
 obtain ⟨hk,c₀,b⟩:= a.core x _ ∅ (subset_refl _) (by simp [Lattice.halo])
 refine ⟨fair_port _ _ _ _ c₀ hk,fun t i h=> b (fun e=>t ?_) _ (List.mem_toFinset.mp h)⟩
 funext v; change fair _=_; rw[e]; exact fair0
lemma rQpen (x: Heart L.anchor S L.d): oV ((L.pureT V T).termR x)= L.rockT x:=funext fun i=> congrArg fair (a.tag x i T)
include t y l p u
lemma pay3_r :Pits σ (L.pureT V T) c g w P r h K:=by
 refine ⟨⟨fun x e _ => ?_,fun x e _ hx=> ?_⟩,⟨fun x Y h=> ?_,fun _ _ _ v=>False.elim (v rfl)⟩,l⟩
 · unfold PitR; rw [rQpen V L T σ a x]; dsimp only [pureT]; convert! (primal L σ a x).1 using 1; congr 1; exact List.toFinset_card_of_nodup (uS_b σ e)
 · refine ⟨mem_filter.mpr ⟨mem_univ _,pays_z σ e⟩,(primal L σ a x).2 (fun e=>hx ?_)⟩; funext i; exact congrFun e (i,T)
 refine ⟨Medal.big Medal.zeroT ?_,fun i e=>False.elim (e rfl)⟩; exact div_nonneg (mul_nonneg (mul_nonneg l (prod_nonneg fun i _=>t _)) (prod_nonneg fun i _=>y _)) (pow_nonneg u.le _)
include q
lemma pay3_b :Pits σ (L.busyT V) (2*c) g w P r h K:=by
 refine ⟨⟨(fun _ _ h=>by contradiction), (fun _ _ h=>by contradiction)⟩,?_,mul_nonneg zero_le_two l⟩
 let κ:= Lattice.halo K (n:=More n)
 have Gone(x:Ψ)(z:Finset β)(i:Orbit n)(p:(∏ j∈z,V.K j) i=0): L.fillT V x z i=0:=by
    unfold fillT; dsimp only; change fair _- ((ite _ _ 0):Copy n) _= _; rw [p, Subalgebra.coe_zero,mul_zero,fair0]; split_ifs; · rw[Pi.mul_apply,p,mul_zero,sub_zero]
    rw [Pi.zero_apply,sub_zero]
 refine ⟨fun x b hb=>?_, fun x b hb a'=>?_⟩
 · let z:= b.val; let O:= R0 x; let D:=til V.z z; let X:=Xd x z; let F:=∏ j∈z,V.K j; let A:=aΓ x; let B:=∏ j∈z,w j; let J:= L.from_ x; let C':= Bplain J.length A r; let W:= V.legend z; let U:= Bplain W.length B r
   change Medal P X D (L.fillT V x z) h _ ∧_
   refine ⟨?_,fun i v=> ((Mica.someL V O z q i (fun t' => v (Gone x z i t'))).symm)⟩ -- fix calls
   have hu: 0≤ C':= div_nonneg (mul_nonneg l (prod_nonneg fun i _=>t _)) (pow_nonneg u.le _); have hf:0≤U:=div_nonneg (prod_nonneg fun _ _=> y _) (pow_nonneg u.le _)
   let R:= C'*U
   apply Medal.big (a:=C'*U+C'*U) -- inspect args
   · by_cases ht:F=0; · rw [show L.fillT V x z=0 from (funext fun i=> Gone x z i (congrFun ht _))]; exact Medal.big Medal.zeroT (add_nonneg (mul_nonneg hu hf) (mul_nonneg hu hf))
     have hk:∃ i,F i ≠0:= Function.ne_iff.mp ht
     obtain ⟨i,v⟩:= hk; have hs:Vx x ⊆ X:= Finset.subset_union_left; have hK:=a.core x X D hs (Mica.someL V O z q i v).1
     let V0:=L.issue x X D
     have Hp:= zero_le_one.trans p; have hp0:= Mica.make_Q V O z true q b.property Hp
     change Medal P X D ((fun i=> fair (V0 i*(F i).val)) - (if Disjoint O.val.2 D then L.rockT x * F else 0)) _ _; rw [sub_eq_add_neg]; refine Medal.plus (fair_port P X D (V0*(fun i=>(F i).val)) (Portμ.mult hK.2.1 (colorIn P _ _ _ hp0 p) hu) (opThemeTimes hK.1 (opThemeHold _ hp0.toThemeR))) (Medal.negT ?_)
     change Medal P X D (ite _ _ 0) h _; split_ifs with h
     · exact Medal.cross (((L.primal σ a x).1).stretchB hs (empty_subset _) (fun i p=> let v:= (mem_sdiff.mp p).1; mem_sdiff.mpr ⟨hs v,fun g=>disjoint_left.mp h v g⟩)) hp0 Hp
     exact Medal.big Medal.zeroT (mul_nonneg hu hf)
   apply le_of_eq; have he: (J++W).toFinset.card=(J++W).length:= List.toFinset_card_of_nodup (uS_b σ hb)
   change R+R=Bplain (J++W).toFinset.card (2*c*(∏ j:Fin L.d,g ((x:Ψ).val j))*B) r; rw[he,List.length_append]; unfold R C' U Bplain A; rw[pow_add]; ring -- ring_div
 · let O:=R0 x; let z:=b.val; let D:=til V.z z; let X:=Xd x z
   have ht:(∏ j∈ z,V.K j)≠0:=fun e=> a' (funext fun i=>Gone x z i (congrFun e i)); have hp:∃ i,(∏ j∈ z,V.K j) i≠0:=Function.ne_iff.mp ht; obtain ⟨i,v⟩:=hp
   have hs:Vx x ⊆ X:= subset_union_left
   refine ⟨mem_filter.mpr ⟨mem_univ _, pays_z σ hb⟩,fun j p=>?_⟩; rcases List.mem_append.mp (List.mem_toFinset.mp p) with p|p
   · by_contra g'
     have e:L.issue x X D=0:= Classical.byContradiction fun e=>g' ((a.core x X D hs (Mica.someL V O z q i v).1).2.2 e _ p)
     have hu:L.rockT x=0:= Classical.byContradiction (fun h=>g' (hs ((primal L σ a x).2 h j (List.mem_toFinset.mpr p))))
     apply a'; funext k; unfold busyT fillT; dsimp only; change fair _ - _ = _; rw[e,Pi.zero_apply,zero_mul,fair0,hu,zero_mul]; simp
   exact Mica.see_M V O z q ht j p
end
end Tuner
end Ivey
end YM.CF.Scree.Ing
end
