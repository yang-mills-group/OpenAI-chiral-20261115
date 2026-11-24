import SatinThinRadiant
set_option autoImplicit false
set_option maxHeartbeats 440000
noncomputable section

namespace YM.ZecaSky
open Function Metric Filter Asymptotics Set
open scoped ComplexOrder InnerProductSpace BigOperators Topology

open Lattice Regis.Head.Brecht Regis.Circuit Stationary

/- spectral analytic extension. explicit totalized norm square parameter l. -/
def bill (j i:Axis)(x:Axis→ℂ)(l:ℂ):ℂ:=
 -2 * Maxwell.normal * (basis j i) * l⁻¹^2 +
      8 * Maxwell.normal * (x j * x i) * l⁻¹^3
abbrev curlIn (a b c d:Axis)(x:Axis→ℂ)(l:ℂ):=
 ((if c=b then bill a d x l else 0)-(if d=b then bill a c x l else 0))
def stamp (p q:PlaqAxes)(x:Axis→ℂ)(l:ℂ):=
 curlIn p.val.1 p.val.2 q.val.1 q.val.2 x l -
 curlIn p.val.2 p.val.1 q.val.1 q.val.2 x l
def satire (z:PlaqAxes→ℝ)(G:Gauge)(x:Axis→ℂ)(l:ℂ):=
 wholeV z (fun p q=>duoPower G (stamp p q x l))

lemma satire_in (z:PlaqAxes→ℝ)(G:Gauge)(x:Gaia)(h:x≠0):
    spectrumℓ z G x = satire z G (fun i=>x i) (↑(‖x‖^2):ℂ):=by
    have hc (p q:PlaqAxes):
       specter p q x=stamp p q (fun i=>x i) (↑(‖x‖^2):ℂ):=by

      simp only [specter,Maxwell.bareCurl, Pi.sub_apply, Maxwell.Bare.opp_grad h, Maxwell.second_Green h,stamp,curlIn,bill]
      push_cast; simp_rw [apply_ite ((↑):ℝ→ℂ)]; push_cast; rfl
    simp only [spectrumℓ,spectrumColor,hc,satire]

section
variable {α:Type*}[NormedAddCommGroup α][NormedSpace ℂ α] {s:Set α}
def TapMotion(x:α→Axis→ℂ)(l:α→ℂ)(s:Set α):Prop:=
 (∀i,DifferentiableOn ℂ (fun z=>x z i) s)∧DifferentiableOn ℂ l s∧∀z∈s,l z ≠ 0
lemma bill_d (j i:Axis)
 (x:α→Axis→ℂ)(l:α→ℂ)
 (g: TapMotion x l s):
 DifferentiableOn ℂ (fun u=> bill j i (x u) (l u)) s:=by
   rcases g with ⟨a,d,e⟩
   have h:DifferentiableOn ℂ (fun z=> (l z)⁻¹) s:= d.inv e
   unfold bill; fun_prop
lemma curlIn_d (a b c d:Axis)
 (x:α→Axis→ℂ)(l:α→ℂ)
 (g: TapMotion x l s):
 DifferentiableOn ℂ (fun u=>curlIn a b c d (x u) (l u)) s:=by
   unfold curlIn; split_ifs <;> refine DifferentiableOn.sub ?_ ?_ <;>
      first | exact bill_d _ _ _ _ g | exact differentiableOn_const _

lemma satire_d (z:PlaqAxes→ℝ)(G:Gauge)
 (x:α→Axis→ℂ)(l:α→ℂ)
 (g: TapMotion x l s):
 DifferentiableOn ℂ (fun u=>satire z G (x u) (l u)) s:=by
   have d:∀a b c d,DifferentiableOn ℂ (fun u=>curlIn a b c d (x u) (l u)) s:=
          fun _ _ _ _=>curlIn_d _ _ _ _ _ _ g
   unfold satire stamp duoPower wholeV; fun_prop
end
#print axioms satire_d
#print axioms satire_in
