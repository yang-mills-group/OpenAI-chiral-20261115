import Bay.D.Aurum
import Bay.D.Puffin
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff
open Regis Regis.Head Etch Gleam Next.SectorChange Next.SectorChange.Gaussian
open Pressure Work.F03 ProbabilityTheory
local notation "T4"=>SU.group
open Resonance Brecht Circuit
open CF.Onyx CF.Ember
open Stationary (Gaia)
open Maxwell

section
variable {n:Side}
   {q:Clip}{H:Bed}{Z:PathData T4}{η C S:ℝ}
   {B:Z.Bounds q η C S}{P:Attached H Z}
 {p:BudgetPoint} {β v M N E L:ℝ}
 {F:Yn n ℂ}{W:Chalk n ℂ}
lemma Ion.sole {o d:Site n}
 (u:Ion B P p β v o o F W M N E L):
    Ion B P p β v o d F W M N E L:=
 ⟨u.perks,u.sane,u.gauge,u.limit,u.gloss,u.high,fun I _ g h=>u.alloy I g ⟨h.1,h.1⟩,
 u.spins,fun A V Y g α δ f m _=>u.day A V Y g α δ f m m⟩
lemma Ion.keel {o d:Site n}
 (u:Ion B P p β v d d F W M N E L):
    Ion B P p β v o d F W M N E L:=
 ⟨u.perks,u.sane,u.gauge,u.limit,u.gloss,u.high,fun I _ g h=>u.alloy I g ⟨h.2,h.2⟩,
 u.spins,fun A V Y g α δ f _ m=>u.day A V Y g α δ f m m⟩

abbrev strata (F:Yn n ℂ)(g h: Kite n):Fin 3→ Yn n ℂ:=
 ![F ∘ g.swirl,star (F ∘ h.swirl),(F ∘ g.swirl)*star (F ∘ h.swirl)]


abbrev ink (W:Chalk n ℂ)(g h: Kite n):Fin 3→ Chalk n ℂ:=
 ![fun u=> W (u*g),star (fun u=> W (u*h)),
       (fun u=> W (u*g))*star (fun u=> W (u*h))]
def caramel (B:Z.Bounds q η C S)(P:Attached H Z)(W: Dock n → ℂ):=
     ∫x:stamen B P n,W x ∂stdGaussian (stamen B P n)
lemma inked (B:Z.Bounds q η C S)(P:Attached H Z)(W:Chalk n ℂ)
  (g h: Kite n)(i:Fin 3):
 caramel B P ((ink W g h i) 1) =
 caramel B P (![W g,star (W h),W g*star (W h)] i):=by
 fin_cases i
 · change caramel B P (W (1*g))=caramel B P (W g)
   rw[one_mul]
 · change caramel B P (star (W (1*h)))=caramel B P (star (W h))
   rw[one_mul]
 change caramel B P ((W (1*g))* star (W (1*h)))=_
 rw[one_mul,one_mul];rfl

lemma Ion.caramel_scale{o d:Site n} (u:Ion B P p β v o d F W M N E L)
    (f:ℂ→L[ℝ]ℝ):
   flavor B P (fun g=> f ∘ W g)=f (caramel B P (W 1)):=by
 unfold flavor caramel clouds

 exact f.integral_comp_comm 
  (Integrable.mono' (integrable_const N)
    ((u.gloss 1).continuous.comp continuous_subtype_val).aestronglyMeasurable (ae_of_all _ fun x=>u.high 1 _))


/-- Eligibility. Over fixed anchors. -/
def Cider(B:Z.Bounds q η C S)(P:Attached H Z)
  (p:BudgetPoint)(x β:ℝ)(o d:Site n)(F:Yn n ℂ)(μ:ℂ):Prop:=
 ∀ f:ℂ→L[ℝ]ℝ, (∀y,‖f y‖≤‖y‖)→ ∃T, Candle B P p x β o d (f ∘ F) T ∧ flavor B P T=f μ

lemma cider_go{o d:Site n}{x:ℝ}
    (u:Candle B P p x β o d F W):Cider B P p x β o d F (caramel B P (W 1)):=by
   change Ion _ _ _ _ _ _ _ _ _ _ _ _ _ at u
   intro f e;exact ⟨_,u.paint _ e,u.caramel_scale f⟩

variable {o:Site n}{x:ℝ}
lemma strata_go (u:Torch B P p x β o F W)(v:Cake.sweet x) (g h:Kite n)
    (i:Fin 3):
   Cider B P p x β (g.rise o) (h.rise o)
        (strata F g h i) (caramel B P (![W g,star (W h),W g*star (W h)] i)):=by
 rw[←inked]
 apply cider_go
 change Ion _ _ _ _ _ _ _ _ _ _ _ _ _ at u
 obtain ⟨a,b,c,d,e,f,k,l⟩:=v
 fin_cases i
 · exact ((u.shift g).relax a b c d).sole
 · exact ((u.shift h).cream.relax a b c d).keel
 exact ((u.shift g).hinge (u.shift h).cream).relax e f k l
end

def Mist (q:Clip)(D σ v r f ε x:ℝ)(m:ℕ):Prop:= 0<x ∧
 ∀ {H:Bed}{Z:PathData T4}{η C S:ℝ}(B:Z.Bounds q η C S)(P:Attached H Z)
    {N:Side}{o b c:Seat N}{p:BudgetPoint}{β d:ℝ}
    {A:Icey (Cella (More N))}{F:Pane N→ℂ}{R:ℕ},
     H.covered σ v → Floor H q (More N) D v →
     p.B=radiusB x → p.threshold=temp x →
     x/2≤β→ β≤2*x →
     Vessel p o (p.B/10) r d f F A →
     Bore (More N) m (p.B/10) R o b c → (R:ℝ)≤reedR x →
     let g:=forward b; let h:=after c
     let U:= wheel (Real.sqrt x) F
     let ρ:= Real.sqrt x * coupling β
     let W:=crop B P ρ (bWindow x) A b c
     (∀j:Fin 3,Cider B P p x β (g.rise o) (h.rise o) (strata U g h j) (W j))∧
     CrownRank x R ε (lscore ρ A) W

theorem mists(q:Clip)(D σ v r f ε:ℝ)
   (t:0<ε)(a:0<σ)(u:0<v)(z:0<r):
 ∃m, ∀ᶠ x in atTop, Mist q D σ v r f ε x m:=by
 obtain ⟨m,w⟩:=golden q D σ v f ε t a u
 refine ⟨m,?_⟩
 filter_upwards[w,wheelAwards q f r z] with x h k
 exact ⟨k.2.1, fun {H Z η C S} B P {N o' b c pe β d A F R} hc fl he hb b₁ b₂ o y p=> ⟨
   strata_go (k.2.2 B P _ hb he _ b₁ b₂ _ _ _ _ _ o) k.1 _ _,
   h _ _ B P hc fl o.2.rake y p (railB b₁ b₂ k.2.1)⟩⟩

end YM.CF.Bay.D
#print axioms YM.CF.Bay.D.mists
