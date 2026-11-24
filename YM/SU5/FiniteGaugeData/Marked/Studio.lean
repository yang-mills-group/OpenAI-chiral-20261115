import YM.SU5.FiniteGaugeData.Marked.Receipt

/-!
# FiniteGaugeData use. With proved (by other assignment) calibration IDs, converge on that
same elected course, with the certified finite expression on all points on the
cone of the returned sequences and the entire inner tail of each selected row.
NB: outside participation (for example the tiniest cutoff on the largest
volume), conventions are merely total functions in `Settled`: no signed
nonvanishing assertion there.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py.Rate Py.Rate.LocalLimit Burn
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
namespace Coupling
open Preparation
variable {K: Calibration} {C:Conveyor K}{J:Tiling K}{V:SpanCal K}(W:Printed K C J V)
local notation "H"=> W.narrative.hist
variable {Λ : Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) (u π:ℕ→ℕ)
variable (S:Schedule K C Λ Y u π)
local notation "β" i:max => Λ.Ctor (Y.ir (u i)) 0

def score (i k:ℕ)(F:Family K) : ℂ:=
  let m:=Y.ir (u i); let n:=Y.uv (π k); let R:=(Y.voyage (u i)).CapeT 0; let X:= ((Y.voyage (u i)).X n).gram 0
  let g:Buffered.Mark (Λ.Ctor m 0):= (S.scale i) ▸ F m
  (∫ x,inner ℂ (Dial.mateK (Λ.Ctor m 0)) (acts (g (drawn R x)) (denZ X Λ.U R x)) ∂ city _)/partitionZ X Λ.U R

/-- Whole receipt on the given physical calibration. Includes finite reading
and actual denominator even for the wider Borel system. -/
structure Stage (P:Process K)(i k:ℕ→ℕ)(A:ℕ→ℕ)(E:Family K→ℂ): Prop where
  periods : P.m=Y.ir ∘ u ∘ i
  uv : P.n=fun _=> Y.uv ∘ π ∘ k
  one_uv : P.n=fun _=> A
  increaseUV : StrictMono A
  thinI : StrictMono i
  thinK : StrictMono k
  increaseP : StrictMono (fun n=> (P.m n).val)
  settled : Settled W.narrative.hist P true E
  /-- Points certified on the cone (hence also inner tails). -/
  docket (a b:ℕ) (h:(P.m a).val^5 ≤ A b): let x:=u (i a); let t:=π (k b); let ν:=(Y.voyage x)
      let m:=Y.ir x; let n:= Λ.Ctor m 0; let c:=Y.uv t; let X:= (ν.X c).gram 0; let R:=ν.CapeT 0
      ν.kick ≤ t ∧ K.Allowed m c ∧ partitionZ (C.sharp m c 0) K.P (C.loom m 0)=partitionZ X Λ.U R ∧ partitionZ X Λ.U R ≠ 0 ∧
      ∀ (F:Family K),TestFamily K true F→ let g:Mark (Λ.Ctor (Y.ir (u (i a))) 0):= (S.scale (i a)) ▸ F (Y.ir (u (i a)))
        Integrable (fun z=> inner ℂ (Dial.mateK n) (acts (g (drawn R z)) (denZ X Λ.U R z))) (city n) ∧
        P.atUV W.narrative.hist a b F=score Y u π S (i a) (k b) F

namespace Studio
include S
lemma result (m:StrictMono u)(n:StrictMono π): ∃ (P:Process K)(i k A:ℕ→ℕ)(E:Family K→ℂ), Stage W Y u π S P i k A E:=by
  let c:=S.carried W m n -- order
  obtain ⟨i,k,p,E,h,e⟩:=c.marquee (fun i k=> (Y.voyage (u i)).kick ≤ π k)
    (fun x=> n.tendsto_atTop.eventually_ge_atTop _)
  refine ⟨p.night,i,k,Y.uv ∘ π ∘ k,E,rfl,rfl,rfl,Y.uv_grows.comp (n.comp p.ζ),p.γ,p.ζ,c.ir.comp p.γ,h,?_⟩
  intro a b v x t ξ M N C X R
  have H':=p.funds a b v; let U:= e a b v; have Hf:= Schedule.mains W S (i a) (k b) U H'
  exact ⟨U,H'.allowed,Hf.1,Hf.2⟩


/- Can ask for actual reading limits in the conclusion too. -/
lemma performed {P:Process K}{i k A:ℕ→ℕ}{E:Family K→ℂ}(T:Stage W Y u π S P i k A E)(F:Family K)(h:TestFamily K true F):
    let ξ a b:= score Y u π S (i a) (k b) F
    (∃ Z:ℕ→ℂ,(∀ᶠ r in atTop,Tendsto (ξ r) atTop (𝓝 (Z r))) ∧ Tendsto Z atTop (𝓝 (E F))) ∧
    (∀ v:ℕ→ℕ,(∀ᶠ r in atTop,(P.m r).val^5 ≤ A (v r)) → Tendsto (fun r=> ξ r (v r)) atTop (𝓝 (E F))) := by
  intro X; obtain ⟨Z,h₁,H'⟩:= T.settled.convergence F h
  constructor
  · exact ⟨Z,h₁.mono (fun r t=> t.congr' ((T.increaseUV.tendsto_atTop.eventually_ge_atTop ((P.m r).val^5)).mono (fun b hr=> ((T.docket r b hr).2.2.2.2 F h).2))),H'⟩
  intro v h₁; obtain ⟨n,hp,Q⟩:= T.settled.joint rfl
  have hn:n=A:= congrFun (hp.symm.trans T.one_uv) 0; rw [hn] at Q
  refine (Q F h v h₁).congr' ?_; exact h₁.mono (fun r u=> ((T.docket r (v r) u).2.2.2.2 F h).2)

omit S
/-- e.g. the same inputs as the FiniteGaugeData joint receipt, re-exported together
with this convergence application on *its* course and (optionally) taken
on exactly its gauge sequences before further marked thinning. -/
theorem encore (ε:ℝ) :
    ∃ (Λ:Preparation)(l:ℕ), ε < Λ.x ∧ Λ.nominated (VolumeCape.Dream.Nimbus l) ∧
      ∃ (Y : Course Λ (VolumeCape.Dream.Nimbus l)),
        (∃ z, Usable (D:=Λ.δ) Λ.V Λ.W Λ.J Λ.N0 z Λ.delay Y.meter) ∧
        (∀ i k, ((Y.voyage i).X k).Prepared Λ.P Λ.delay) ∧
        (∀ i j:ℕ, LoomLaw ((Y.voyage i).CapeT j) (YM.SU5.FiniteGaugeData.Audit1102.lawRadius (VolumeCape.Dream.plot l).C)) ∧
        ∃ u π:ℕ→ℕ, StrictMono u ∧ StrictMono π ∧ Nonempty (Y.Query u π) ∧
          ∀ (K:Calibration)(C:Conveyor K)(J:Tiling K)(V:SpanCal K)(W:Printed K C J V)(ID:Schedule K C Λ Y u π),
            ∃ (P:Process K)(i k A:ℕ→ℕ)(E:Family K→ℂ), Stage W Y u π ID P i k A E ∧
             ∀(n:ℕ)(F:Fin n→eligible K true), E 1=1 ∧ (Matrix.of fun i j=> E (thetaK K (F i).val*(F j).val)).PosSemidef := by
  obtain ⟨Λ,l,v,H',Y,m,p,c,u,π,g,h,x⟩:=Py.Rate.Audit1102.same_physical_history ε
  refine ⟨Λ,l,v,H',Y,m,p,c,u,π,g,h,x,fun K C J V W S=>?_⟩
  obtain ⟨P,i,k,A,E,T⟩:= result W Y u π S g h
  exact ⟨P,i,k,A,E,T,fun _ F'=> Concert.gram W T.settled F'⟩
end Studio
end Coupling
end YM.CF.Buffered.Afterglow
#print axioms YM.CF.Buffered.Afterglow.Coupling.Studio.encore
#print axioms YM.CF.Buffered.Afterglow.Coupling.Studio.performed
