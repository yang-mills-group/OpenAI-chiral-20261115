import GaugeFieldConstruction.Photon3
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
attribute [local instance] boreKSpace boreXN opCStarAlgebra
variable {R:Loom n}{k:ℕ}{t d a c e r h:ℝ} 
variable (F:Elm n Unit d a c)(R:Loom n)(k:ℕ)(t:ℝ)
-- halves option. Cell width one.V orientation motion.
variable (X S D:Support (More n))(W:Orbit n)
local notation "Vx"=> uplift F R k D S t
local notation "Y"=> Single n
local notation "GL"=> LeanV (Single n)
variable (u:Roof n t d k R)(q:0<d)
variable (o:Seat n) (Z:Paper n)(p:L3 n)
local notation "Zd"=> Pach o
local notation "L"=> pack3 k o p
variable (P:BudgetPoint){g H h K0 T:ℝ}(ψ:Hann P k t)(v:pure_Rim F) (z: TrackD (Py.KeyUp P) (Pach o) h Z g)(w:portable Z)
local notation "K"=> ArchQ F R k t P o p Z
local notation "γ1" W:max=> Elev F R k t D W
noncomputable def RiceV(S:Support (More n))(A:Paper n)(p:L3 n)(D:Support (More n))(V:Orbit n): FC (Dwell n):= wax (αLines A V.1) p (Elev F R k t D V)
local notation "Rν"=> RiceV F R k t X Z p D
-- Quals at Exact argument, all including ties. Issue Full.Health
variable (tZ:(pack3 k o p).val.2 ⊆ X)(hμ:Lattice.halo (cipherK k) D⊆ X)
include tZ hμ u q
private lemma roomPin(x:SP3 n)(s:limbM k x⊆ X)(i:LeanV (Single n)){V₁ V₂:Orbit n}(h:Lattice.Agrees X V₁.1 V₂.1)(v:Set.EqOn V₁.2 V₂.2 X) : pinMode (Elev F R k t D V₁) x i=pinMode (Elev F R k t D V₂) x i:=by
 cases x
 · change put i=put i; rfl
 next S=>
    --
    change iceK (χH F R k t S V₁ D) i=iceK (χH F R k t S V₂ D) i; have ht:uplift F R k D S t V₁=uplift F R k D S t V₂:= lift_eq u hμ s q h v; unfold χH gainH giftH; rw[ht]
-- domain
omit u q tZ hμ
include z
lemma label_μ (V:Pane n)(i:Wa n)(v:αLines Z V i ≠0): DomainP (Pach o) i:=Classical.byContradiction (fun x=> v (show Z i V=0 from congrFun (z.choose_spec.1 i|>.2 x) _)) -- tune
include u q v w tZ hμ
lemma Wit_A : OpTheme X (RiceV F R k t X Z p D) false:=by
 have p':Pach o ⊆ X:= subset_union_left.trans tZ
 refine ⟨fun a b c d=>?_,fun x=>?_,?_,fun i j=>?_⟩
 · have V: αLines Z a.1= αLines Z b.1:=funext fun i=> (z.choose_spec.1 i).1.2.2.1 _ _ (agrees_mono c p')
   have hg(i:Wa n): tokenMode (Elev F R k t D a) p i=tokenMode (Elev F R k t D b) p i:=by
      cases i with
      | none=>change (if τPure p then (_:FC (Dwell n)) else _)= _; exact rfl
      | some i=>
         rcases i with ⟨tb,j,s⟩
         change pinMode (Elev F R k t D a) p.1 (tb,j)*pinMode (Elev F R k t D a) p.2 (!tb,s)= pinMode (Elev F R k t D b) p.1 (tb,j)*pinMode (Elev F R k t D b) p.2 (!tb,s)
         exact congrArg₂ (· * ·) (roomPin F R k t X D u q o p tZ hμ p.1 ((subset_union_left.trans subset_union_right).trans tZ) (tb,j) (V₁:=a) (V₂:=b) c d) (roomPin F R k t X D u q o p tZ hμ p.2 ((subset_union_right.trans subset_union_right).trans tZ) (!tb,s) (V₁:=a) (V₂:=b) c d)
   unfold RiceV wax; rw[V]; exact sum_congr rfl fun i _=>congrArg (αLines Z b.1 i • ·) (hg i)
 · have h:=label_μ o Z P z x.1; exact lift_v (ψMesa k o p (γ1 x) (αLines Z x.1) h (fun S i j v=>(chin_i F R k _ S D x u q i j v).2)) (camp_b tZ)
 · have hp(v:SP3 n)(j:LeanV (Single n)): Measurable (fun x:Orbit n=>pinMode (γ1 x) v j):=by
       cases v; exact measurable_const
       next S=> exact σΔ F R k t S D u q j
   unfold RiceV wax; apply Finset.measurable_fun_sum; intro i _; refine ((z.choose_spec.1 i|>.1.2.1).1.comp measurable_fst).smul ?_ -- args annon
   cases i with
   | none=> exact measurable_const
   | some i=> exact (hp p.1 _).mul (hp p.2 _) -- tune
 change wax _ _ _=lotY false false _ _; unfold RiceV; rw [show αLines Z (Lattice.gauge j i.1)=_ from w i.1 j]; exact (Gaugeq3 F R k t D i u q p v j _).symm
-- arithmetic singulars
local notation "Mφ"=>Portμ (citrus P X D) (0:tangD n)
variable (tK:hud_T 7 K0)(b':0≤T)(e':coinH K0 T)(t':1≤h)
omit v w
omit tZ
include ψ tK b' e' t'
abbrev KernelLeg (x:SP3 n) (F:Elm n Unit d a c)(T h:ℝ):ℝ:= x.elim 1 (fun S=> BillLeg S d T a c F/h^2)
omit z hμ
lemma Kp_h (v:SP3 n): 0 ≤ KernelLeg v F T h:=by
    rcases v with _|S; exact zero_le_one
    exact div_nonneg (Vegan3 F R k t S u q b') (sq_nonneg h)
include hμ
lemma PNail (x:SP3 n)(j:LeanV (Single n))(H:limbM k x⊆ X): Mφ (fun i=>pinMode (γ1 i) x j) h (h * KernelLeg x F T h) P.order:=by
 rcases x with _|S; · rw[KernelLeg,Option.elim_none,mul_one]; exact mist_p P.order _ h (0:tangD n) j t'
 apply (Υμ F R k t X S D u q ψ tK e' b' t' H hμ j).rise _ (zero_le_one.trans t') -- tune arg order. 
 unfold KernelLeg; rw [Option.elim_some]; apply le_of_eq; field_simp
include tZ
abbrev taxPair (p:L3 n)(F:Elm n Unit d a c)(T h:ℝ):= KernelLeg p.1 F T h*KernelLeg p.2 F T h
lemma VBill(i:Wa n):Mφ (fun x=> tokenMode (γ1 x) p i) h (taxPair p F T h * papW n h i) P.order:=by
 have hp(x):= Kp_h F R k t u q P ψ tK b' e' t' x; let O:=taxPair p F T h
 obtain (_|⟨b,i,j⟩):=i
 · change Mφ (fun _=> ite _ _ _) h _ P.order
   split
   next p'=>
      have ht: p=(none,none):=Prod.ext (Option.isNone_iff_eq_none.mp ((Bool.and_eq_true _ _).mp p').1) (Option.isNone_iff_eq_none.mp ((Bool.and_eq_true _ _).mp p').2)
      -- rewrite only cost
      rw [show (taxPair p F T h* papW n h none)=1 from (by rw [ht]; change 1*1*1= (1:ℝ); ring)]
      exact Portμ.const _ (Ark.one h)
   exact (Portμ.zero h 0).rise (mul_nonneg (mul_nonneg (hp _) (hp _)) (papW_v _)) (zero_le_one.trans t')
 have ht:= PNail F R k t X D u q P ψ hμ tK b' e' t' p.1 (b,i) ((subset_union_left.trans subset_union_right).trans tZ)
 have hx:= PNail F R k t X D u q P ψ hμ tK b' e' t' p.2 (!b,j) ((subset_union_right.trans subset_union_right).trans tZ)
 refine (ht.mult hx (mul_nonneg (zero_le_one.trans t') (hp p.1))).rise (le_of_eq ?_) (zero_le_one.trans t'); change _= _*_*h^2; ring
-- Mark weights pay.P within.KeyUp
include z
local notation "L0"=> (z.choose)
lemma plusZ (i:Wa n)(q:Disjoint (Pach o) D)(x:Lime P X D): Pence P.order (fun y=> Z i (citrus P X D x y).1) (0:tangD n) (7* z.choose i):=by
 let f:=citrus P X D x; have he: pingS ((Py.KeyUp P).threshold) (Pach o) x.val.1.1:= grow_b (fun a b=> mem_sdiff.mpr ⟨tZ (subset_union_left b),fun g=> disjoint_left.mp q b g⟩) x.property.1
 have ht:= z.choose_spec.1 i |>.1.2.2.2 x.val.1.1 he
 let L':= Rill.unrest x.val.2 P.B; let A:=Forge.wakeB (G:=SU.group) L'; have hp:‖A‖≤1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v=> by rw [one_mul]; apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2; intro i; unfold A; rw [Forge.steadyB]; split; exact norm_le_pi_norm v i; exact norm_zero.le.trans (norm_nonneg _) -- arg vibes.
 let F' := (Z i) ∘ Shield.solo ((Py.KeyUp P).threshold) x.val.1.1
 have hv:= Rue.bare_p _ _ (XGarden.comps A (x:=0) (show Allows P.order F' (A 0) (z.choose i) from (map_zero A).symm ▸ ht) hp)
 apply Pence.germ (Pence.mono (B:=7* L0 i) hv (le_of_eq (by rw [ψ.canon]; norm_num))); refine Eventually.of_forall (fun a=> ?_)
 change Z i (increment _ (_ • Forge.wakeB L' a))=Z i (increment _ (Forge.wakeB L' (_ • a))); rw [map_smul]
-- pay aura allot
lemma ant3 (δ: Disjoint (Pach o) D): Mφ (RiceV F R k t X Z p D) h (taxPair p F T h * 7 * g) P.order:=by
 let c:=taxPair p F T h; let O:= Elev F R k t D; let V(i:Wa n)(u:Orbit n):= Z i u.1 • tokenMode (O u) p i; let B(i):=(7*z.choose i)*(c*papW n h i)
 have hp(i): Mφ (V i) h (B i) P.order:= Portμ.scale (VBill F R k t X D u q o p P ψ tZ hμ tK b' e' t' i) (fun x:Orbit n=>Z i x.1) (mul_nonneg (by norm_num) (z.choose_spec.1 i|>.1.1)) (fun j=> plusZ R k t X D u q o Z p P ψ z tZ hμ tK b' e' t' i δ j) -- tune.F? omit explicit vars.
 have ht:Rν=∑ i:Wa n,V i:=funext fun i=>Eq.symm (Finset.sum_apply ..)
 rw[ht]; apply (Portμ.sum _ _ _ (fun i _=>hp i)).rise _ (zero_le_one.trans t')
 have hx(v):0≤KernelLeg v F T h:=Kp_h F R k t u q P ψ tK b' e' t' v
 apply le_trans _ (mul_le_mul_of_nonneg_left z.choose_spec.2 (mul_nonneg (mul_nonneg (hx p.1) (hx p.2)) (show (0:ℝ)≤ 7 by norm_num))); rw [Finset.mul_sum]; apply sum_le_sum; intro i _; unfold B c taxPair; exact le_of_eq (by ring)
-- ensure pure.Mark proofs
omit tZ hμ
include v w
local notation "R'"=> ArchQ F R k t P o p Z
noncomputable def pay_A (o:Seat n)(Z:Elm n Unit d a c)(b h g:ℝ)(p:L3 n):ℝ:= if warmMode o p then taxPair p Z b h* 7 *g else 0
lemma PercentT : 0≤ pay_A o F T h g p:=by
 unfold pay_A; split; next x=>
    have hx(i):= Kp_h F R k t u q P ψ tK b' e' t' i; exact mul_nonneg (mul_nonneg (mul_nonneg (hx p.1) (hx p.2)) (by norm_num)) (track_pos z)
 rfl
lemma Act_Γ(pZ:24≤P.B) : Act3 (ArchQ F R k t P o p Z) P (cipherK k) h (pay_A o F T h g p) :=by
 have hx(W):= label_μ o Z P z W
 let f(D:Support (More n)) := Elev F R k t D
 let K':= ArchQ F R k t P o p Z
 constructor
 · intro X D g x; change OpTheme X _ _∧Portμ (citrus P X D) (0:tangD n) _ h _ P.order; unfold ArchQ; dsimp only; split
   next a=> rw [pay_A,if_pos a.2]; exact ⟨(Wit_A F R k t X D u q o Z p P v z w g x), ant3 F R k t X D u q o Z p P ψ z g x tK b' e' t' a.1⟩ -- tune
   next v'=> exact ⟨opTheme0 _ _,(Portμ.zero h 0).rise (PercentT F R k t u q o Z p P ψ v z w tK b' e' t') (zero_le_one.trans t')⟩
 · intro T T'; unfold ArchQ; dsimp only; split; swap; · rfl
   let h:=f ∅ T; let h':=f ∅ (T.1,T'); change wax _ _ h'=wax _ _ h; have he:h=h':= funext fun t=>by change χH _ _ _ _ _ _ _= _; unfold χH gainH giftH; rw [lift_empty (F:=F) u q (S:=t) (U:=T) (T:=T')]
   exact congrArg (fun t=> wax _ _ t) he.symm
 -- verify meaning in Oasis at Fleet.
 · intro X D W h ht m g'; let Yz:=Pach o; have hx:Yz⊆ X:= subset_union_left.trans ht
   have hu:pingS P.threshold (Pach o) W.1 ↔ Disjoint (Pach o) D:=by
      have hp:= shoreK P.threshold W.1 h Yz; change Disjoint Yz (flags P.threshold W.1) ↔ _ at hp; refine hp.symm.trans ?_; constructor; intro p; exact Disjoint.mono_right (g' ▸ inter_subset_right) p; intro k; exact Finset.disjoint_left.mpr fun i t w=> Finset.disjoint_left.mp k t (g' ▸ mem_inter.mpr ⟨hx t,w⟩)
   unfold ArchQ; dsimp only; simp only [hu]; split_ifs with hP; swap; · rfl
   have he(A:SP3 n)(g:limbM k A⊆ X)(i:LeanV (Single n)) : pinMode (Elev F R k t D W) A i=pinMode (fun S=>rawH F R S W) A i:=by
      cases A; · change put i=put i; rfl
      next X' =>
       have v:pingS P.threshold (X\D) W.1:=(shoreK _ _ h _).1 (show Disjoint (_:Support _) (flags P.threshold W.1) from Finset.disjoint_left.mpr fun v p q=> (mem_sdiff.mp p).2 (g' ▸ mem_inter.mpr ⟨(mem_sdiff.mp p).1,q⟩))
       change iceK (Elev _ _ _ _ _ _ X') i=iceK (rawH F R X' W) i
       have ht':uplift F R k D X' t W=releaseQ F X' (R W):= if_pos (Rill.CreekX.payz ψ.pitch m g v)
       unfold Elev χH gainH giftH rawH -- tune
       rw [ht']
   let f:= (fun S=>rawH F R S W); let E:= (Elev F R k t D W)
   change wax (αLines Z W.1) p E = _; apply sum_congr rfl; intro i _; refine congrArg (fun y₀:FC (Dwell n)=>αLines Z W.1 i • y₀) (show tokenMode E p i=tokenMode f p i from ?_); cases i with
   | none=> change (ite _ (_: FC _) _) = _; exact rfl
   | some i=> exact congrArg₂ (· * ·) (he p.1 ((subset_union_left.trans subset_union_right).trans ht) (i.1,i.2.1)) (he p.2 ((subset_union_right.trans subset_union_right).trans ht) (!i.1,i.2.2))
 · intro U p0; change Sector _ false (ite _ _ _); split; swap
   · exact Sector.zero _
   next v'=>exact ψMesa k o p _ _ (hx U.1) (fun S i j qp=> (raw_i F R k t S U u q _ _ qp).2)
 · intro U; change rank2 (ite _ _ _); split; exact canon_φ _ _ (αLines Z U.1); intro i j s; simp [bump]
 intro U P'; change Flour _ (ite _ _ _); split; swap
 next t'=> exact Flour.trivial
 next q' =>
   rw [pure_H_τ _ p Z U.1 P']; have he:= sprig o z (show (Py.KeyUp P).power≤ _ from le_rfl) (by show P.order≤ _; exact ψ.canon.le) w; exact ((rimR he (zero_le_one.trans t')).lit U).lift (camp_b (show Pach o⊆ (pack3 k o p).val.2 from subset_union_left)) -- tune.Br.
#print axioms Act_Γ
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end
