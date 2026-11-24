import Merino.Lustre
import YM.SU5.Exchange.Visa.Moon
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino
open Filter Topology Lattice Lat Tulip Branch Cube Tenant Drapes Metric
open _root_.Zephyr.Chern
open scoped Matrix Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Finset Swell

variable {n:Side}

open Py.Rate.LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
open Skye Scree Vale RG
open Py (hueW stemS pinpr)



universe u

/-- All promises in the same election argument, retaining prospective
multi-root loans, not inserting them as premises to existence.
`Mc` from (the finite library-size application of)
`planetaryPolar`. The x is the chosen vacuum data, NOT the fixed terminal coupling,
which is in P.par. Certifying X before both limits is part of selecting a Spine,
not here claiming a prescription for any externally supplied numeric X. -/
structure Gala (P:Spine)(K:P.Register)(x:P.Spectrum0 3)(Mc:ℕ) : Prop where
  joint: Spine.JointTuple.{u} P K x
  tiled: 8 ∣ P.par.M.val
  roster: P.Roster
  hears: RateStamp P.run
  pleases: Compass_sol P.run
  samples: SprigFee P
  forward: ∃ (Pay kc G : ℝ)(Tξ:Hove.Grant P.par.K.j 2)(n:ℕ),
    Sweepcraft P.run Tξ Pay kc G n Mc


theorem grand (Mc:ℕ) : ∃ P K x,Gala.{u} P K x Mc:=by
  obtain ⟨P,K,x,H,A,B,C,D⟩:=Spine.planetaryPolar.{u} Mc
  have ro:P.Roster:=by
    obtain ⟨c,r,R,i,F,U,X,n,w,V,g,h,X',Y,Z,m₁,m₂,m₃,m₄,m₅,j,f,e,q,b,li⟩:=H
    exact li.roster
  exact ⟨P,K,x,H,A,ro,B,C,SprigFee.paid P,D⟩

/-- Keeping a default base point and mesh. Others available through
the underlying promises. -/
structure Palais (P:Spine)(p:Bolts) : Prop where
  long:0<priceTick P
  spacing(s i:ℕ):2*priceTick P ∣ (RegNum P s i).val
  terminal(i k:ℕ):(LedgerM P 0 i k).beta=P.par.x
  forecast(s i k:ℕ)(h:s≤P.run.uv k): (LedgerM P s i k).p=P.run.meter.a s ∧
      matchedX (scaleM P s) (LedgerM P s i k).beta
  grant:woven P (priceTick P) p
  light:shines P (priceTick P) p

lemma Gala.arms {P:Spine}{K:P.Register}{x:P.Spectrum0 3}{Mc:ℕ}
    (h:Gala P K x Mc): ∃ p, Palais P p:=by
  have y:0<priceTick P:=Nat.mul_pos (by norm_num) P.par.block.property
  obtain ⟨p,w⟩:=weave P (priceTick P) h.roster h.pleases h.hears
  exact ⟨p,y,frame_fit P h.tiled,terminal_beta P,
    fun _ _ _=>calibrated P,w,litUp P _ p h.samples y w⟩

/-- Physical simultaneous origin version; spelling out what it gives
at scales s, i, k. `Glowing` and `Dress` are on the same consultation,
charging the same scalar and normalization. -/
lemma Palais.earns {P:Spine}{p:Bolts}(h:Palais P p):
    ∃ δ E:ℝ,0<δ∧0<E ∧∀ᶠ s in atTop,∀ᶠ i in atTop,∀ k,
      (P.run.voyage i).kick≤k → s<P.run.uv k →
      ∃ d:Dress P s i k p (priceTick P) (wrap (RegNum P s i) zeroBase),
        Glowing P (priceTick P) p zeroBase s i k δ E d:=by
  obtain ⟨δ,E,t,u,v⟩:=h.light zeroBase
  refine ⟨δ,E,t,u,v.mono fun s z=>z.mono fun i l k a b=>l k ⟨a,b⟩⟩
end YM.CF.Merino
