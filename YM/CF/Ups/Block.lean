import YM.CF.Ups.Ichor
set_option autoImplicit false
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
variable {d e η z g A B':ℝ} {k k' m n l:ℕ}
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
open Oath Feu Feu.Corset Ione Nor Haro Beau Salt Vow
set_option maxHeartbeats 800000
variable {U:Grasp V.U B d}{W:GivenX V U}
variable (a:ℝ)(p i N0 k₀:ℕ)
variable {N':Side}(J:Robes N' V W)(q:Chi)(h:ℝ)(R0 δ:ℝ→ℝ)
local notation "Lr"=>dleaf R.L
open CF.Mint MeasureTheory
variable {x':ℕ→ℝ}(t:Tendsto x' atTop atTop){L':ℕ→ℕ} (U':∀ i',SpanPS V a p i N0 J q h R0 δ (x' i') (L' i'))
local notation "N_X"=> rimZ V N0 J (x':=x')
variable(X:Month x a i p N0 V W) (H:MeterQ V a p i N0 J q h R0 δ x X)
open Graph
local notation "Mo"=> oYY V N0 J x
local notation "Zo" j:max=>cell Mo B R.L j
variable {ℓ:ℝ}(hp:1≤h)(ht:0 <ℓ)(hx:0 < x)
open Pyx Girt
local notation "hatQ"=> hat R.L x
variable (L0:∀ l:ℕ,SpanPS V a p i N0 J q h R0 δ x l)(R':Cape (oYY V N0 J x) B R.L)(Q:CoilPS V a p i N0 J q h R0 δ X L0 R')
variable {β:ℕ→ℝ}{A:ℕ→Haro.SpaceM}{F:∀ i,InkPS (cell (oYY V N0 J x) B R.L i)}{u:ℕ→ℕ}
local notation "Eρ"=> ν_P V a p i N0 J q h R0 δ L0 R'
variable (dF:ΦS_P V a p i N0 J q h R0 δ L0 R' β A F u)(hpF:K.top.clip.direct ≤1)
local notation "Fp"=> PionK V Mo B R' q
local notation "Lp₀" j:max=> InkPS (Zo j)
local notation "T₀" j:max=> Oracle (Zo j)
open Reed
variable (j:ℕ)(O:Oracle (cell (oYY V N0 J x) B R.L j))(Pb:BoundedT O)(Px:Loyal O) (Pc:RealC O)
abbrev SongO {N:Side}(O:Oracle N):Prop:= BoundedT O∧ Loyal O∧RealC O
abbrev BornO {N:Side}(O:Oracle N):Prop:=∃ (X Y:Orbit N→FC (Single N)), Reed.LampC O X Y ∧ ∀ g:Skye.Seat N→ SU.E,∀ p:Orbit N,X (gird g p)= twist (quantU (tradew _ g)) (X p)∧ Y (gird g p)= twist (quantU (tradew _ g)) (Y p)
lemma read_C {N:Side}(X:Oracle N)(h:SongO X): BornO X:=by
 obtain ⟨p,Q,g⟩:= clan_PS X h.2.2 h.1; exact ⟨p,Q,g,fun i p=> camp_x X g p (gird i p) i (h.2.1 _ _)⟩
include Q dF Pb Px Pc j
structure Dawns(W:∀ k:ℕ,Oracle (cell (oYY V N0 J x) B R.L (j+k)))(X:ℕ→Haro.SpaceM)(Bv:ℕ→ℝ)(F:∀ i,InkPS (cell (oYY V N0 J x) B R.L i)): Prop where
 bill(k:ℕ):SongO (W k)
 stake : W 0=O
 pond(k:ℕ):BornO (W k)
 cruise(k:ℕ): let V₀: j+k.succ=j+k+1:=rfl; ActsPS V N0 J q R' (j+k) (W k) (W (k+1)) (Bv (j+k+1)) (X (j+k))
 grant(k:ℕ): remark O (F j)=remark (W k) (F (j+k))
lemma spore_u :∃ Λ, Dawns V N0 J q R' j O Λ A β F:=by
 let Y(k:ℕ):= {Q:Oracle (Zo (j+k)) // SongO Q}; have hx(k:ℕ)(pu:Y k):∃ w:Y (k+1), ActsPS V N0 J q R' (j+k) pu.val w.val (β (j+k+1)) (A (j+k)) ∧ remark pu.val (F (j+k))=remark w.val (F (j+k+1)):=by
    obtain ⟨X,b,x,h1,pP,K⟩:= hand_PS V a p i N0 J q h R0 δ X L0 R' Q dF (j+k) _ pu.property.1 pu.property.2.2 pu.property.2.1 -- shadows
    exact ⟨⟨X,h1,x,pP⟩,b,K⟩
 choose g hM using hx; let X:(k:ℕ)→ Y k:=Nat.rec (⟨O,Pb,Px,Pc⟩: Y 0) g
 refine ⟨fun k=>(X k).val,⟨fun i=> (X i).property,rfl,fun i=>read_C _ (X i).property,fun k=> (hM k (X k)).1,?_⟩⟩
 intro k; induction k with | zero => exact rfl|succ k ih=> exact ih.trans (hM k (X k)).2
omit dF -- finite. version k shift fixed scope.Add.Br.
structure BornU {N:Side}(O:Pyx.Track N) (X Y: Pane N→FC (Single N)): Prop where
 lamp: Reed.LampC O X Y
 move(g:Skye.Seat N→ SU.E)(p:Pane N): X (Lattice.gauge g p)=twist (quantU (tradew N g)) (X p)∧Y (Lattice.gauge g p)= twist (quantU (tradew N g)) (Y p)
include hpF
-- from each Λ to top, Gibbs continuum cylinder pair.Frame.Corpus. Test equality of linear evals; NOT algebra at IR.
lemma flamePS(k:ℕ): let v:=j+k; let Y:= L0 v;∃ (H: Pyx.Track (cell (oYY V N0 J x) B R.L v)) (X Z:Pane (cell (oYY V N0 J x) B R.L v)→ FC (Single (cell (oYY V N0 J x) B R.L v))), BornU H X Z ∧ let K : Pane (cell (oYY V N0 J x) B R.L v)→ Phys (cell (oYY V N0 J x) B R.L v):=fun z=> (partitionZ (Y.E v) U (Y.Y v))⁻¹ • (Vale.capP (K:=K) U ((Y.E v).beta) (Y.val.a v) z (m:=Vale.mesh (oYY V N0 J x) R.L v)); (∫ i:Orbit (cell (oYY V N0 J x) B R.L j), O i (Eρ j v i) ∂city _)=(∫ x',H x' (K x') ∂prior SU.group _):=by
 intro z Z'; let D:= Z'.scale; let K:= Z'.Y; let Y(t):= Z'.E t; have he(t):R' t=K t:=(congrFun (Q.tale z) t).symm
 let A(t):= ω_den U (Y t) (K t)
 let F'(t):= partitionZ (Y t) U (K t); let Lc:= F' z
 let Qκ:= lon V Mo j U (Y j) (K j) O; have ht'(p:ℕ)(hl:p≤k): ∃ Ψ:Oracle (Zo (j+p)), SongO Ψ∧ Qκ= lon V Mo (j+p) U (Y (j+p)) (K (j+p)) Ψ:=by
    induction p with
    | zero=> exact ⟨O,⟨Pb,Px,Pc⟩,rfl⟩
    | succ t' ih=>
       obtain ⟨X,⟨pQ,g,b0⟩,ξ⟩:=ih (by omega); let y:=j+t'; have hj:y < z:=by unfold y z; omega
       obtain ⟨D'⟩:=Brioche.us V Z'.tip J q h D y hj; have he:= Brioche.drives V Z'.tip J q h D y; let S:=V.L.op (z-1-y) (kint Mo B R.L y); let A:=Z'.Q y
       obtain ⟨W,pW,P⟩:= boardQ D' he.1 he.2 (barQ A pQ); exact ⟨W,⟨P,heart D' S he.1 he.2 pW (frock _ g),χPS pW b0⟩, ξ.trans (Pyx.ticket D' (p:=he.1) (t:=he.2) pQ _ pW ((D.note.owns _ (by omega:y ≤ z)).width ▸ D.mark _) (D.note.wear _ hj))⟩
 obtain ⟨Ψ,⟨p,g,w⟩,hQ⟩:=ht' k le_rfl; obtain ⟨H,wΛ,u⟩:= crus_e Ψ p; have hc:= planet Ψ H wΛ g; have hp:ScalarC H:=by
    intro i x t; rw [wΛ i,wΛ i]; simp_rw [w (i,_)]; exact integral_smul ..
 obtain ⟨X',v,hψ⟩:= clan_PS H hp u; refine ⟨H,X',v,⟨hψ,(fun g p=> camp_x _ hψ p _ g (hc g p))⟩,?_⟩ -- order tune ctor
 intro f; obtain ⟨s,hx⟩:= Brioche.hot V Z'.tip J q h D hpF; have hZ:Envelope f:=by
    let UQ:= Classical.arbitrary (Ids (Zo z)); let g(x:Pane (Zo z)):=denZ (Y z) U (K z) (x,UQ); have hb: Envelope g:= Girt.snap (X:=fun i:Pane (Zo z) => (i,UQ)) s (by fun_prop)
    have he(i:Pane (Zo z)):f i= Lc⁻¹ • g i:=by unfold g; rw [show denZ _ _ _ _ = _ from hx (i,UQ)]
    rw [funext he]; exact Girt.pole_w _ (fun i=> Lc⁻¹ • i) (continuous_const_smul _) hb
 change (∫ x,O x _∂city _) =∫ y,H y (f y)∂prior SU.group _; rw [bowK Ψ p H wΛ _ hZ]; let x:= Y j; rw [show Eρ j z= ω_den U x (K j) from by rw [←he]]; have hu(j:Orbit (Zo z)): f j.1=A z j:=by unfold A ω_den f; rw [show denZ _ _ _ _= _ from hx j] -- tune
 simp_rw [hu]; unfold A ω_den; simp_rw [show partitionZ x U (K j)= Lc from D.balance j (by unfold z; omega), Pc,w,integral_smul]; exact congrArg (Lc⁻¹ • ·) hQ
end YM.CF.Py
