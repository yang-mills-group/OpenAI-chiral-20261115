import GaugeFieldConstruction.Tunes3
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
open Tuner
variable (V:RegLime I α n)(A:Factor3 n)(Q:LeaseQ γ n)(σ:I→Seat n)(k:I)
variable (p d:ℕ)(y:Hub n)(T:Heart A.H Q.H p)
local notation "Rφ"=> Legist y V.S d
local notation "Θv"=> Heart y V.S d
local notation "Ωt" x:max X:max=> filmic V A Q p d T y x X
variable (x:Heart y V.S d)
abbrev ζβ(D:Support (More n)):= Sum.elim (fun a=> V.K a (V.S a∩D)) (fun i=>Q.issue i D)
-- Tune.Sem actual uses Ω fed as full. Ark realm.PEC
variable (P:BudgetPoint)
abbrev origin3 : Orbit n→(x:Heart y V.S d)→ FC (Dwell n):=fun W x=> discount p d • (scar (A.raw W) ((List.ofFn fun i=> V.K (x.val i) (flags P.threshold W.1) W)++ (List.ofFn fun j=> Q.raw (T.val j) W)))
local notation "αΓ"=> Π i:I,I -- not used
variable {r h s:ℝ}{g:α→ℝ}{l:γ→ℝ}{K:ℕ}(u:RegPay V P σ r h g)(v:Act3 A P K h s)(L:Leased Q P K h l)
variable (b:ScopeΔ A Q p T y) (ht:p+d≤ fadeN A)(Z:σ k∈y.val.2)
local notation "Yg"=> loomR V A Q p d T y x
local notation "Kπ"=> peatE V A Q k p d ht T y
abbrev zcost3(h:ℝ)(p d:ℕ)(r:ℝ)(B:ℝ):= ‖discount p d‖* (2:ℝ)^(d+p)* h * r * B
local notation "D5"=> Dwell n
section
include u
lemma μ_occ (D X:Support (More n))(g': (Legist y V.S d x).val.2 ⊆ X)(e:(Ωt x D)≠0): ∀ i∈ tags V d y x,σ i∈X :=by
 let Z:=loomR V A Q p d T y x; intro i b; obtain ⟨j,_,m⟩:=(roster_mem ..).1 b
 have h: V.K (x.val j) D ≠0:=fun g=> e (funext fun i=>by
    let q:= Sum.inl (β:=γ) (x.val j); have hx:q∈Z:=List.mem_append_left _ (List.mem_ofFn.mpr ⟨j,rfl⟩); have hv(i):stamps V Q D q i=0 :=congrFun g i
    change discount _ _ • scar _ (Z.map fun j=> stamps V Q D j i)= 0
    have hw: (0:Cipher n) ∈ Z.map (fun j=> stamps V Q D j i):= List.mem_map.mpr ⟨q,hx,hv i⟩
    rw [scar_perm _ ((List.perm_cons_erase hw).trans (List.perm_append_singleton _ _).symm), scar_append, show scar (A.issue D i) [0]=0 from (by unfold scar; simp [scar,bump]), scar_blank, smul_zero])
 exact g' (νt V d y x j (u.qual _ _ h i (List.mem_toFinset.mpr m)))
omit u in
lemma rosterLen(r:ℝ)(x:Heart y V.S d): r^(tags V d y x).length=∏ j:Fin d,r^(V.V (x.val j)).length :=by
 let B: Fin d → List I:=fun j=> V.V (x.val j)
 have hp(L:List ℕ): r^L.sum=(L.map fun i=>r^i).prod:=by induction L with | nil=>simp| cons t l h=>rw[List.sum_cons,pow_add,h,List.map_cons,List.prod_cons]
 unfold tags rosterF; rw [List.length_flatten,List.map_map,hp,List.map_map]; change (Finset.univ.toList.map (fun j=>r^(B j).length)).prod=_
 rw[← List.prod_toFinset (fun j=>r^(B j).length) (Finset.nodup_toList _)]; simp; rfl
include u v L b
lemma payout3 (x:Heart y V.S d)(X D:Support (More n))(t:(Legist y V.S d x).val.2⊆X)(w:Lattice.halo K D⊆ X)(h0:1≤h)(hg:0 ≤ g)(hV:0 ≤ l)(u0:0 ≤ s)(hr:0<r): Portμ (citrus P X D) 0 (filmic V A Q p d T y x D) h (Bplain (k::tags V d y x).length (zcost3 s p d r (∏ j:Fin p,l (T.val j)) * ∏ j:Fin d,g (x.val j)) r) P.order ∧ OpTheme X (filmic V A Q p d T y x D) false:=by
 let L₀(i):=Bplain (V.V i).length (g i) r; let M:= loomR V A Q p d T y x
 obtain ⟨a,k'⟩:=μ_pay V A Q σ p d T y x u L v b X D t w h0 hg hV u0 hr
 refine ⟨a.rise ?_ (zero_le_one.trans h0),k'⟩; unfold loomR -- tune M not occurrence lhs
 simp only [List.length_append,List.map_append,List.map_ofFn,List.prod_append,List.length_ofFn]
 rw[List.prod_ofFn,List.prod_ofFn,List.length_cons]; unfold Bplain zcost3; rw[pow_succ, rosterLen V]
 have he : (∏ j:Fin d,g (x.val j)/r^(V.V (x.val j)).length)=(∏ j:Fin d,g (x.val j))/(∏ j:Fin d,r^(V.V (x.val j)).length):=by rw[prod_div_distrib]
 dsimp only [Function.comp_apply,Sum.elim_inl,Sum.elim_inr]; rw [he]; apply le_of_eq; field_simp
include Z ht
lemma Paid3 (h0:1≤h)(hg:0 ≤ g)(hV:0 ≤ l)(u0:0 ≤ s)(hr:0<r): accords (peatE V A Q k p d ht T y) P σ r h (zcost3 s p d r (∏ j:Fin p,l (T.val j))) K g:=by
 refine ⟨fun x X D e op=>?_,fun x U T'=>?_⟩ -- shadow p
 · skip
   have ht:=payout3 V A Q σ k p d y T P u v L b x X D e op h0 hg hV u0 hr
   refine ⟨ht.2,ht.1,fun t i w=>?_⟩; rcases List.mem_cons.mp w with w|w
   · rw [w]; exact e (subset_union_left Z)
   exact μ_occ V A Q σ p d y T x P u _ _ e t i w
 -- tag
 change discount _ _ • scar _ _= discount _ _ • scar _ _; rw [v.turf _ _]; congr 2
 apply List.map_congr_left; intro i b; cases i with | inl i=> exact u.turf _ _ _| inr i=> exact L.mint _ _ _ -- tune
omit Z
lemma query3: oasis (peatE V A Q k p d ht T y) P K (origin3 V A Q p d y T P):=by
 have Fk(x:Θv)(W:Orbit n)(w:Rue.FleetS P.threshold W.1)(X D:Support (More n))(t:(Legist y V.S d x).val.2⊆ X)(P0:X∩flags P.threshold W.1=D)(u':Lattice.halo K D⊆X): filmic V A Q p d T y x D W=origin3 V A Q p d y T P W x:=by
    have h' :y.val.2⊆X:= subset_union_left.trans t
    change discount _ _ • scar (A.issue D W) _= discount _ _ • scar _ _
    rw[v.ready _ _ _ w (b.1.trans h') u' P0]; congr 2 -- tune lists
    simp_rw [loomR,List.map_append,List.map_ofFn]; congr 2 -- specific f equal
    · funext i; let K:=x.val i; let Ω:= flags P.threshold W.1; change V.K K D W=_; have p':V.S K⊆X:= (νt V _ _ x i).trans t; refine congrFun (u.meet _ _ _ ?_) W; rw[←P0,← inter_assoc,inter_eq_left.mpr p']
    funext j; exact L.speak _ _ _ _ w ((b.2 j).trans h') u' P0
 refine ⟨fun x W v X D t q f=>Fk x W v X D t q f,fun x W v'=>?_⟩
 -- sector append TRUE even deduction.Support proof Need Q.H⊆Q.X to get final.S.
 let Z:=Legist y V.S d x; let M:= Z.val.2
 have ho(D0:List (Cipher n))(h:∀ i∈D0,Fock.Sector (camp M) false i.val): Fock.Sector (camp M) false (scar (A.raw W) D0):=by
    induction D0 with
    |nil=> exact lift_v (v.qual W v') (camp_b (b.1.trans subset_union_left))
    |cons i D0 ih=> have y:=ih (fun i q=>h i (List.mem_cons_of_mem _ q)); have ht:=h _ List.mem_cons_self; rw [scar,bump,sub_eq_add_neg,←one_smul ℂ (i.val*_),←neg_smul]; exact (y.mul ht).add ((ht.mul y).scale _)
 refine Fock.Sector.scale ?_ _; apply ho; intro i h; rcases List.mem_append.mp h with h|h <;> (obtain ⟨j,rfl⟩:=List.mem_ofFn.mp h)
 · exact lift_v (life ((u.wine (x.val j) (flags P.threshold W.1)).lit W)) (camp_b (νt V d y x j))
 exact lift_v (L.qual _ _) (camp_b ((L.later _).trans ((b.2 j).trans subset_union_left)))
end
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end
