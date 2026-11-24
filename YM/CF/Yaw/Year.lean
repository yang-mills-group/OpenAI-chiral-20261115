import YM.CF.Yaw.Trust
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Yaw
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake
open Scion PetalP
open scoped Classical
variable {ι A n M:Type}[Fintype ι][DecidableEq ι][Fintype A][DecidableEq A][LinearOrder n][Fintype n][LinearOrder M][Fintype M]
local notation "K"=> LeanV M
local notation "vext"=> (twigExt : LeanV n ↪ Twig n)
local notation "veau"=> (twigCab : Oboe n ↪ Twig n)
variable {J:n→A}{D:LeanV M→A}{X:ι→ leaf A}{P:Finset ι}{a:Crowd A}
local notation "H₀"=> Crowd A
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{z:E}{k:ℕ}
variable {B:Raid (LeanV M)}{Q:Twig n→ Track (Crowd A) ℝ}{c:Twig n→ Track (Crowd A) (Raid (LeanV M))}{w:Twig n→Twig n→ Track (Crowd A) (Raid (LeanV M))}{U:PetalP (LeanV n)}{L:PetalP (Oboe n)} {b:Raid (LeanV M)}
-- budgets factored across P. permit voice stock data & scale on same Hearth
abbrev PoolL (A:List ι)(B:ι→ Raid (LeanV M)):Raid (LeanV M):= A.foldr (fun i b=>skirt (B i) b) (Pi.single ∅ 1)
lemma wpos(A:List ι)(B:ι → Raid K) (p:∀ i∈A,0≤B i): 0 ≤ PoolL A B:=by induction A with| nil=> intro i; unfold PoolL; rw [List.foldr_nil]; rw [Pi.single_apply]; split_ifs; exact zero_le_one; exact le_rfl| cons i A H=> exact skirtPos _ _ (p _ (List.mem_cons_self ..)) (H (fun i v=>p i (List.mem_cons_of_mem _ v)))
lemma wsize(A:List ι)(W:ι→Raid K)(p:∀ i∈A,0≤ W i)(v: Turner B) : joinV B (PoolL A W)≤ (A.map (fun i=>joinV B (W i))).prod:=by
 induction A with
 | nil=> unfold PoolL; rw [List.foldr_nil]; rw [joinVone v]; exact v.red
 | cons i A ih=> have hu:= p i (List.mem_cons_self ..); have hv (i)(v:i∈A):0≤ W i:=p i (List.mem_cons_of_mem _ v); refine (turnS v _ _ hu (wpos A _ hv)).trans (mul_le_mul_of_nonneg_left (ih hv) ?_); exact sum_nonneg fun i _=> mul_nonneg (v.fee _) (hu _)
lemma wphys(A:List ι)(W:ι→ Raid (LeanV M))(X:ι→ E→FC K)(h:∀ i∈A,Woody k (X i) z (W i)): Woody k (A.map X).prod z (PoolL A W):=by induction A with| nil=> exact Woody.uniV _| cons i A ih=> exact (h _ (List.mem_cons_self ..)).pairP (ih (fun i v=>h i (List.mem_cons_of_mem _ v)))
variable (r:List ι)(U:ι→ PetalP (LeanV n))(L:ι→ PetalP (Oboe n))(W:ι→ Raid (LeanV M))(B Q)
local notation "nod"=> r.Nodup
local notation "key"=> r.toFinset
lemma petpos(r:List ι){n:Type}(U:ι→ PetalP n)(p:∀ i∈r,0≤(U i).led):0 ≤ (PetalP.Ribbon r U).led:=by induction r with| nil=> exact fun i=>zero_le_one| cons i l ih=> intro j; change (tw _ _).slots at j; exact mul_nonneg (p i (List.mem_cons_self ..) (Prod.fst j)) (ih (fun j v=>p j (List.mem_cons_of_mem _ v)) (Prod.snd j))
lemma sh_h {u: Type}(U:PetalP u)(p:0≤U.led)(F:u→ Track H₀ ℝ)(g:∀ i,0≤ F i): 0 ≤ share U F:= sum_nonneg fun i _=> smul_nonneg (p i) (pay_S g)
abbrev beamZ(X:ι→ leaf A)(B:ι→ℝ)(i:ι):Track H₀ ℝ:=Pi.single (beamH (X i).val) (B i)
lemma crankK (h:ℝ)(p:Crowd A)(x:ℝ)(a:Crowd A): crank (Pi.single p x) (Pi.single a h)=Pi.single (p⊔a) (x*h):=by funext i; apply proves; intro j _; simp_rw [view_crank,singleV,sup_le_iff]; simp only [ite_mul,zero_mul,mul_ite,mul_zero,ite_and]; split_ifs<;>simp [*]
lemma paysK (g:ι→ℝ) (X:ι→leaf A):payH (beamZ X g) r=Pi.single (cluster X (r.toFinset)) (r.map g).prod:=by induction r with | nil=> unfold payH cluster; rw [List.toFinset_nil,sup_empty]; rfl| cons i l ih=> rw [List.map_cons,List.prod_cons,List.toFinset_cons]; exact (congrArg (crank (beamZ X g i)) ih).trans ((crankK ..).trans (by rw [show cluster X (insert i l.toFinset)= _ from Finset.sup_insert]))
lemma crane (F G:ι→ Track H₀ ℝ)(r: List ι):crank (payH F r) (payH G r)=payH (fun i=>crank (F i) (G i)) r:=by
 induction r with
 | nil=> exact crank_L _
 | cons i l ih=> change crank (crank (F i) (payH F l)) (crank (G i) (payH G l))=crank (crank (F i) (G i)) _; rw [crank_A, ←crank_A (payH F l), crank_C (G i), crank_A _ (payH F l),ih, ←crank_A (F i)] -- tune
variable (X)
def dawnT (i:ι):= crank (crank (share (U i) (Q∘vext)) (share (L i) (Q∘veau))) (beamZ X (fun i=>joinV B (W i)) i)
include J D
lemma prism_p (p: OfferS B Q c w)(f:∀ i∈r,0≤ (U i).led)(v:∀ i∈ r,0≤ (L i).led)(u:∀ i∈ r,0≤ W i):∃ K':Track H₀ (Raid K),0≤K' ∧ rateT B K' ≤ payH (dawnT X B Q U L W) r ∧∀(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](a:H₀)(z:E)(k:ℕ)(F:E→ ribbon M),(z∈ tsupport F→ ∃ X_:E→ ModeW J D X r.toFinset,PactW z k a (Ribbon r U) (Ribbon r L) X_ c w (PoolL r W) ∧∀ᶠ y in 𝓝 z,F y=vigor (X_ y) a)→Woody k (fun x=>(F x).val) z (K' a):=by -- declaration order X U etc, Ribbon amb brace
 obtain ⟨Kb,l,b,u'⟩:=paysP (J:=J) (D:=D) (X:=X) (P:=r.toFinset) p (petpos _ _ f) (petpos _ _ v) (wpos _ _ u); refine ⟨Kb,l,b.trans ?_,u'⟩ -- ambiguity K token!
 apply le_trans (crank_mono _ _ (Pi.single (cluster X r.toFinset) ((r.map (fun i=>joinV B (W i))).prod) : Track H₀ ℝ) ?_ ?_) ?_
 · exact crank_s _ _ (sh_h _ (petpos _ _ f) _ fun i=> coinH.trans (p.knee _)) (sh_h _ (petpos _ _ v) _ fun i=>coinH.trans (p.knee _))
 · intro i; simp_rw [Pi.single_apply]; split_ifs; exact wsize r W u p.peg; exact le_rfl
 unfold dawnT; rw [← paysK r (fun i=>joinV B (W i)) X, rib_l,rib_l,crane,crane]
end YM.CF.Yaw
