import Anomaly.Contact
import Anomaly.SweepKernel
import YM.SU5.Exchange.Pace.Cult

/-!
Towards (129). First assemble and synchronize a physical source with the
B,budgets on this `run` for the rootwise workings. We choose one set
of truncations and all placements use literally its translates. (Detector
will also require orientation adaptation.)
-/
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
-- In the signature refer also to these exact m,t appointments.
local notation "Θ" s:max=> (hat P.R.L P.x s)
local notation "cap" i:max s:max=> ((Y.voyage i).CapeT s)
local notation "bm" i:max k:max s:max=> RootBook Y i k s
local notation "Ω" i:max s:max=> P.Ctor (Y.ir i) s

structure Spools {N:Side}(o:Site N)(J T: Axis→SOp N)(X Z M V:SOp N)(a b c d:ℝ)(k m:ℕ):Prop where
    hatJ : ∀ i, Trunk (node o) (J i) k a b d
    tailJ : ∀ i,Soak (node o) (T i) a c d
    capX : Trunk (node o) X k a b d
    tailX : Soak (node o) Z a c d
    readsJ(i:Axis)(U:Pane N): Guard U d→spur (millIntro M V) o i m (profile U)=J i (profile U)+T i (profile U)
    readsX(U:Pane N): Guard U d→ (M (profile U)-tickA N)*windmill o m=X (profile U)+Z (profile U)

lemma Spools.transfers {N:Side}{u:Site N}{J T:Axis→ SOp N}{X Z M V:SOp N}{a b c d:ℝ}{k m:ℕ}(p:Spools u J T X Z M V a b c d k m)(t:Staffer M V d)(h:0<d)(o:Site N) :
    Spools o (fun i=>co_Ψ o u (J i)) (fun i=>co_Ψ o u (T i)) (co_Ψ o u X) (co_Ψ o u Z) M V a (Tenant.quota^2*b) (Tenant.quota^2*c) d k m :=
  ⟨fun i=>(p.hatJ i).station o, fun i=> co_Ξ (x:=rfl) o u (p.tailJ i), p.capX.station o, co_Ξ (x:=rfl) o u p.tailX,
   fun i U hx=>co_promise u o _ _ t _ _ (p.readsJ i) h U hx, fun _=>co_wind u o _ _ t p.readsX _⟩

structure Ribbons (b:BudgetPoint)(i k s:ℕ)(m:ℕ)(E T:SOp (Ω i s))(a v d:ℝ)(J Z:Axis→ SOp (Ω i s)):Prop where
    ids : b=(bm i k s).p
    tubes : Spools 0 J Z E T (funde P.K.j (bm i k s).J.M (Ω i s)) (Moire.bloom (bm i k s).J.P) a v (Real.exp (-a*((b.B/10:ℕ):ℝ))*v) d (b.B/10) m

structure CartPins (i k s m:ℕ)(a v:ℝ)(F D:ℝ)(J T : Axis→SOp (Ω i s))(X Z:SOp (Ω i s)) : Prop where
  -- budget-backed second look (width/directional rights for true evaluations by Vita).
  staffing : Staffer (funde P.K.j (bm i k s).J.M (Ω i s)) (Moire.bloom (bm i k s).J.P) P.d
  pulse : DockPulse (bm i k s).p (cap i s) P.J.k P.d a P.h 32 24 P.J.n
  capR : ((bm i k s).p.B/10)+ P.J.n+10 ≤ (bm i k s).p.B
  curtain : 24*m ≤ (bm i k s).p.B
  ropes : Ribbons Y (bm i k s).p i k s m X Z a v P.d J T
  for_all(o:Site (Ω i s)): let J':=fun j:Axis=>co_Ψ o 0 (J j); let X':=co_Ψ o 0 X; let R:=bm i k s; ∃ V:Sour.Bag _,Swell.Nest P.U R (cap i s) P.J.n 24 (node o) P.h (rScale R.p) ((hueW P.R.L (Θ s):ℂ) • puffLine (cap i s) R.p o J' X' m) V F (D*pinpr P.R.L (Θ s))

theorem weighAll (flag:∀ i k, ((Y.voyage i).X k).Prepared P.P P.delay)
    (W:Compass_sol Y) (H:RateStamp Y) (m:ℕ) :
    ∃ a b:ℝ, ∃ F D:ℝ→ℝ, 0<a∧0<b ∧ NPL F ∧ NPL D ∧ ∀ᶠ s : ℕ in atTop,∀ᶠ i : ℕ in atTop,∀ k : ℕ,s<Y.uv k →
      ∃ (J T:Axis→ SOp (Ω i s))(X Z:SOp (Ω i s)), CartPins Y i k s m a b (F (Θ s)) (D (Θ s)) J T X Z:=by
 -- Re-check factorium tariffs under translated disclosures with this increased (fixed) constant.
 obtain ⟨a,b0,c,v,u,ha,hb0,hc,H1,H2,L⟩:= statements Y flag H W m
 let b:=Tenant.quota^2*b0; let p0:= Y.meter.a 0; let U:=coatFull P.R.L p0 m P.h a c b; let V:=coatVoid P.R.L p0 m P.h a c b
 obtain ⟨hz,hX⟩:=coatMoney P.R.L p0 P.h a c b m ha
 refine ⟨a,b0,U,V,ha,hb0,hz,hX,?_⟩
 filter_upwards [L,(turnover P).eventually (draft_π P.R.L),
    (Work.E01.radiusB_tendsto.comp (turnover P)).eventually_ge_atTop (2*(P.J.n+10)+24*m)] with s S σ Θ'; filter_upwards [S] with i p k hk
 let K:= cap i s; let R:=bm i k s; let Q:=R.p; let M:=funde P.K.j R.J.M (Ω i s); let T:= Moire.bloom R.J.P; let w:=Q.B/10; let G:= Real.exp (-a*(w:ℝ))*b; let x := Θ s; let G0:= Real.exp (-a*(w:ℝ))*b0
 obtain ⟨A,H,π,Xs,P',kV,vB,hQ,h0,h2,hP,hV,A',E⟩:=p k hk
 obtain ⟨Jv,Tv,Xv,Zv,hTh,g,l,f,t,vZ⟩:= (E (0:Site (Ω i s))).tickets
 have V':Ribbons Y Q i k s m Xv Zv a b0 P.d Jv Tv:= ⟨rfl,hTh,g,l,f,fun i U h=> t i ⟨profile U,U,h,(by simpa using P.dpos)⟩,fun U h=>vZ ⟨profile U,U,h,by simpa using P.dpos⟩⟩
 have hpQ:2*(P.J.n+10)+24*m≤Q.B:=hQ.symm ▸ Θ'
 refine ⟨Jv,Tv,Xv,Zv,Xs,π,show w+P.J.n+10≤ Q.B from (by unfold w; omega),show 24*m ≤ Q.B from (by omega),V',?_⟩
 intro o J X _
 have he: G=Tenant.quota^2*G0:=by unfold G b G0; ring
 have Ht:Spools o J _ X _ M T a b G P.d w m:= he.symm ▸ V'.tubes.transfers Xs P.dpos o -- tries infer
 let Jd:= fun j:Axis=>co_Ψ o 0 (Tv j); let Y':=co_Ψ o 0 Zv
 -- maybe annotate above.
 let y:= κfront 24 Q 32 P.h a c m; let P₀:=veilPay 24 Q 32 P.h a c b m; let d:= tailPay 24 Q 32 P.h a c G m; let z' := y+d+(P₀+P₀); let X0:= puffLine K Q o J X m
 have hs := Swell.taught_for π Xs Ht.hatJ Ht.tailJ Ht.capX Ht.tailX Ht.readsJ Ht.readsX A H vB
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
