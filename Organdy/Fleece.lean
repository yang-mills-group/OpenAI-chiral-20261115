-- Variant of Prep.factorium exposing explicit prices
import YM.SU5.Exchange.Pace.Cult
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
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
open YM.CF.BPress (PL NPL)
variable {F G:ℝ→ℝ}
open Vow Sour Swell Ione
namespace Rate
namespace LocalLimit
open Jet
namespace Preparation
open FullBill Window Marks
open Pitching Focus QuadClock
variable {P:Preparation}{F:(s:Side)→Scree.Loom s→Prop}(Y:Course P F)
local notation "tape" i:max=> (Y.voyage i)
local notation "Coord" i:max k:max=> (tape i).X (Y.uv k)
variable {Pay ξC Γϕ:ℝ}{n u:ℕ}{Tξ:Hove.Grant P.K.j 2}
variable (flag:∀ i k, ((Y.voyage i).X k).Prepared P.P P.delay)
local notation "xt" => hat P.R.L P.x
local notation "Aκ" v:max=> Y.meter.a v
local notation "Rt" i:max k:max s:max => (RootBook Y i k s)
local notation "Ω" i:max k:max=> cell (Y.ir i) P.block P.R.L k

-- world vial.U.Calendar Pace. scaled sizes using reference p_s real rates after orientation.
local notation "K🌌" s:max=> (Y.meter.a s)
variable {i k s:ℕ}(W:Compass_sol Y) (H:RateStamp Y)(m:ℕ)

include flag H W
-- complete source of pre-seed.Y.Volume. Recover leased stanza entries from same kit at every placement room.
lemma factoriumCoat(m:ℕ): ∃ a c0:ℝ, ∃ (F D:ℝ→ℝ), 0<a∧0<c0 ∧ NPL F ∧ NPL D∧(∃ c,F=coatFull P.R.L (Y.meter.a 0) m P.h a c c0 ∧ D=coatVoid P.R.L (Y.meter.a 0) m P.h a c c0)∧∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k,s<Y.uv k → let K:=(Y.voyage i).CapeT s; let R:=RootBook Y i k s; let P':= R.p; let M:=funde P.K.j R.J.M (cell (Y.ir i) P.block P.R.L s); let S:=Moire.bloom R.J.P; let x:=xt s; let Kw:=P'.B/10; let g:=Real.exp (-a*(Kw:ℝ))*c0; ∀ o:Site (cell (Y.ir i) P.block P.R.L s),∃ J T:Axis→SOp (cell (Y.ir i) P.block P.R.L s),∃ X Y':SOp (cell (Y.ir i) P.block P.R.L s),(∀ i,Trunk (node o) (J i) Kw a c0 P.d)∧(∀ i,Soak (node o) (T i) a g P.d)∧Trunk (node o) X Kw a c0 P.d∧ Soak (node o) Y' a g P.d∧ (∀ l:Axis,∀ z:Openc (More (cell (Y.ir i) P.block P.R.L s)) P.d,spur (millIntro M S) o l m z.val=J l z.val+T l z.val)∧(∀ z:Openc (More (cell (Y.ir i) P.block P.R.L s)) P.d,(M z.val-tickA _)*windmill o m=X z.val+Y' z.val) ∧ ∃ V: Sour.Bag _, Swell.Nest P.U R K P.J.n 24 (node o) P.h (rScale P') ((hueW P.R.L x:ℂ) • puffLine K P' o J X m) V (F x) (D x*pinpr P.R.L x):=by -- ∃ Binder parse
 obtain ⟨a,b,c,v,u,ha,hb,hc,H1,H2,K⟩:= statements Y flag H W m; let p0:=Y.meter.a 0; let U:=coatFull P.R.L p0 m P.h a c b; let V:=coatVoid P.R.L p0 m P.h a c b
 obtain ⟨hz,hX⟩:=coatMoney P.R.L p0 P.h a c b m ha
 refine ⟨a,b,U,V,ha,hb,hz,hX,⟨c,rfl,rfl⟩,?_⟩
 filter_upwards [K,(turnover P).eventually (draft_π P.R.L)] with s S σ; filter_upwards [S] with i p k hk; intro K R Q M T x w G o
 obtain ⟨A,H,π,Z,P',kV,vB,hQ,h0,h2,hP,hV,A',E⟩:=p k hk; obtain ⟨J,T',X,Y',Θ,g,l,f,u,vZ⟩:= (E o).tickets
 refine ⟨J,T',X,Y',Θ,g,l,f,u,vZ,?_⟩
 let y:= κfront 24 Q 32 P.h a c m; let P₀:=veilPay 24 Q 32 P.h a c b m; let d:= tailPay 24 Q 32 P.h a c G m; let z' := y+d+(P₀+P₀); let X0:= puffLine K Q o J X m
 have hs := Swell.taught π Z Θ g l f u vZ A H vB
 let b' := (Q.B:ℝ); have hx:1≤ b':=Nat.one_le_cast.mpr Q.B_pos; let D:=b'⁻¹; have hg:0<D:=by unfold D; positivity
 have he: Fence M T _ _ _ 24 _ P.h (rScale Q+D+D) X0 z' d := downFence (m:=0) hs (rateEx Q)
 have hN:∃ F, Nest P.U R K P.J.n 24 (node o) P.h (rScale Q) X0 F (z'+τΓK Q P.R.L x z') (d+τΓK Q P.R.L x z') :=by
    have hA:= knock P.U R K π.roof P' kV (show 0 ≤ rScale Q from by unfold rScale; positivity) hg he A'
    dsimp only at hA; simpa only [D,inv_inv] using hA -- defeq? tune
 obtain ⟨Fg,t⟩:=hN
 have hvz:p0.order=6:=(Y.meter.boot 0).2.2.2.2; have hwQ:Q.order=p0.order:= h0.trans hvz.symm; have hl:= lifeS P.R.L P.h a c m Q p0 hwQ x hQ z' b -- check arg order
 have htξ:coverT0 p0 m P.h a c b x=d:=by rw [hl.2.1]; unfold d G; rw [tail_linear,coverT0]; unfold exponentialR; rw [←hQ]; -- tune battery price.X Q defeq
 have hw:coverT1 p0 m P.h a c b x = z':=by
    unfold coverT1; rw [htξ]; unfold z' y P₀ primT; obtain ⟨h,h₁,_⟩:=order_v hwQ P.h a c b m; rw [h₁,h]
 obtain ⟨ξ,ht,v,xp,hu⟩:=σ -- using ht maybe implicit galt
 let U':=hueW P.R.L x; have hδ: 0 ≤ U':=by unfold U' hueW stemS; apply mul_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)); exact Real.rpow_nonneg (BPress.drift_pos _|>.le) _
 let Fk:= nestScale P.U R K (↑U':ℂ) t
 refine ⟨_, nestUp P.U R K ?_ ?_ Fk⟩ <;> (change ‖(U':ℂ)‖*_ ≤ _; apply le_of_eq; rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hδ,hl.1,← hw]) -- simp hQ
 unfold V coatVoid; rw [htξ]; exact (div_mul_cancel₀ _ (show pinpr P.R.L x≠0 from ne_of_gt (pow_pos ht 2))).symm
end Preparation
end LocalLimit
end Rate
end YM.CF.Py
