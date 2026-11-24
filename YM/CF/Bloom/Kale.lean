import YM.CF.Bloom.Stage
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Beau Haro Ione Salt
set_option maxHeartbeats 1000000
variable {U:Grasp V.U B d}{W:GivenX V U}
variable (a:ℝ)(p i N0:ℕ)(T:Month x a i p N0 V W)(M:Side)(ht:T.q ≤ M.val)(l0:ℕ)(k₀:ℕ)
variable (B0:ℕ→ℝ)(D:Due V a p i N0 T M ht l0 B0)
variable {N':Side}(J:Robes N' V W)(q:Chi)(h:ℝ)
local notation "Xc"=> cell M B R.L
local notation "Lr"=>dleaf R.L
local notation "Fh"=> hueR V a p i N0 T M ht l0 B0
local notation "μh"=> hat R.L x
abbrev rent_b (i:ℕ):= Lr (μh i)
structure Fossil (P:ℝ)(R0 E C D:ℝ→ℝ)(z:ℝ):Prop where
 step (x:ℝ)(u:z≤x){N P':Side}(S:StepData (Domain N B) (Domain P' B))(G:Ratio (mid N B) (mid P' B))(T: Tube SU.group S)(A0:Scree.Loom (mid N B))(B_:Scree.Loom (mid P' B))(X:GramM (mid N B))(Y: GramM (mid P' B))(pA:Roof _ J.k J.roomX J.n A0)(pB: Roof _ J.k J.roomX J.n B_) (wB:∀ F' U' V', JointB G (seine G F' q J.d U' (A0 V'), A0 V') J.roomX)(H: Girt.BaseL U G Y A0 B_ q J.d) {Z' γ:ℝ} (b:StatV V G T U W X Y Z' γ a x p i) (g:N0*radiusB x ≤ (Domain N B).val)(c:60< (Domain N B).val)(s: Arc_r Y h (dleaf R.L x) (dleaf R.L x) (dleaf R.L x))(m:∃ X', Tact G S Y h (dleaf R.L x) X')(N':BeaconP K.j Y S)(v:Pant_W (N:=P') Y): NovaL V X Y U A0 B_ G S q J.d h (P/(R.L.val:ℝ)*dleaf R.L x+E x) (C x) (D x) (R0 x) R.L.val
 hu:z≥1
 pay(x:ℝ)(u:z≤x):P/(R.L.val:ℝ)*dleaf R.L x+E x ≤ dleaf R.L x∧ C x ≤ dleaf R.L x
 me (x:ℝ)(u:z ≤ x):0< dleaf R.L x∧ ∀ y:ℝ,x≤ y→ dleaf R.L y ≤ dleaf R.L x∧ plow x≤plow y
 rise(x:ℝ)(u:z ≤ x): |D x| ≤ rendK k₀ x
 buying : 8*W.z≤ z
lemma form_X(P:ℝ)(w:P/R.L.val ≤ 1/4)(F:CleaveΘ (p:=p) (k:=i) V U W q a J.d J.n P N0 J.k J.roomX h) (K0:ℕ): ∃ R0 E C D:ℝ→ℝ,sizeK R.L 2 R0∧ Litt R 2 E ∧Litt R 2 C∧ Chill_v D∧∃ z:ℝ,Fossil V a p i N0 K0 J q h P R0 E C D z:=by
 obtain ⟨s,t⟩:=dev_R R; obtain ⟨R0,E,C,D,u,v,a,b,hQ⟩:= F.wrap _ _ _ _ s s s s t
 obtain ⟨x,hX⟩:=eventually_atTop.mp hQ; obtain ⟨y,h,d⟩:= glimp_T (R:=R); obtain ⟨z,hz⟩:= eventually_atTop.mp ((stand_v R P w E C v a).and (fuel_s D b K0)); let x':=max (max (max x y) z) (8*W.z); have hx:x≤x':= le_trans (le_max_left x y) (le_trans (le_max_left ..) (le_max_left ..)); have hu:y≤x':=(le_max_right ..).trans (le_trans (le_max_left ..) (le_max_left ..)); have hp:z ≤x':=le_trans (le_max_right ..) (le_max_left ..)
 exact ⟨R0,E,C,D,u,v,a,b,x',⟨fun x e {N M} S G T A B X Y v f u K {Z κ} b k s t p x0 v0=> hX x (hx.trans e) S G T A B X Y v f u K b k s t p x0 v0, h.trans hu,fun i p=>(hz i (hp.trans p)).1,fun i p=> let t:=d i (hu.trans p); ⟨t.1,t.2.2⟩,fun i p=> (hz i (hp.trans p)).2,le_max_right ..⟩⟩ -- tune shadow x and Imp
local notation "Z"=> (Xc)
open Tap
lemma baseY {w':ℝ}(k:ℕ)(t:0≤w') : Laurel (Fh l0) k h w' w' R.L.val:=by
 let X:= Fh l0; let p:= X.p; have hp: X.F=0:=rfl; have ht: X.slip=0:=rfl; have hv: X.K=0:=rfl
 refine ⟨?_,ht,?_,?_,?_⟩; · change IncX _ X.F _ _ _; rw [hp]; let u:IncX (fun _: Sweep (cell M B R.L l0)=>True) 0 p h 0:= (Vale.lye ..).1; obtain ⟨w,x,g⟩:=u.weight; exact ⟨⟨w,x,fun i=>(g i).trans t⟩,u.face⟩ -- defeq F
 · change Dark _ X.K _ _ _; rw [hv]; let u:Dark (fun _: Sweep (cell M B R.L l0)=>True) 0 p h 0:= (Vale.lye ..).2; obtain ⟨w,x,g⟩:=u.weight; exact ⟨⟨w,x,fun i=>(g i).trans t⟩,u.face⟩ -- fix param n
 · intro i v w; change Beau.spark i.val.1 (0:InkD _); constructor; exact map_zero _; intro x y p v; have ht: pot (∅:Finset (Dwell (cell M B R.L l0))) ∘ (0:InkD (cell M B R.L l0)) ∘ increment 1=(fun _=>0):=funext fun j=> map_zero _; rw [ht]; simp
 have hx:StackL X.F (treeΘ p R.L.val)=0:=by
    apply Finset.sum_eq_zero; intro i t'; rw [hp]; ext u v; unfold orbitPH; rw [Matrix.of_apply,Prism.port_eq]; split; rfl; simp [Pastry.crumb]
 unfold Sour.BondL.mintv; change Tap.NullW (Tap.potion k X.J.M (heroP (StackL X.F _))); rw [hx]; have hz : heroP (0: Op (Single (cell M B R.L l0)))=0:=by unfold heroP Haro.loft Haro.tapH matPH; funext p; apply sum_eq_zero; intro i _; simp [Scroll.tap]
 rw [hz]; have he:Tap.potion k X.J.M 0=0:=by ext; simp [Tap.potion]
 rw [he]; exact ⟨rfl,fun i=> hasDerivAt_const ..⟩
end YM.CF.Py
