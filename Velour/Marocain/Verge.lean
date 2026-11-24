
import Velour.Marocain.Garland
import Velour.Gathers.Rhythm
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 1100
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)

open Boundary Probe

variable {n:ℕ}


local notation "U" => S.unit.translation
local notation "R" => S.gauze
local notation "D" => S.muslin
local notation "B" => S.weight
local notation "𝓧" => Fin n → H.Op
local notation "𝒦" => Fin n → ℕ
local notation "𝓕" => Fin n → Test4
local notation "𝓑" => Module.End ℂ D
local notation "𝓗" => H.space

local notation "G!" => S.heatL
local notation "E!" => S.E
local notation "𝓛" => Fin n → ℝ≥0
local notation "𝓣" => Fin n → S.Detector
local notation "𝓠" => Fin n → ℝ≥0 → H.Op

open Velour

lemma hatch_heat (l r:ℝ≥0)(X:H.Op)(k:ℕ)(f:Test4):
 S.hatch (E! l * X * E! r) k f = G! l * S.hatch X k f * G! r:=by
 rw [S.hatch_eq,S.heat_right_label,S.heat_left_label,S.hatch_eq]
 ext1 v
 change B k (G! l (S.labelled X f (G! r (B k v))))=
     G! l (B k (S.labelled X f (B k (G! r v))))
 rw [S.heat_weight,S.heat_weight]

/-- Padding any field. -/
def enroof (t:S.Detector)(l r:ℝ≥0): S.Detector where
 toFun f:= G! l * t f * G! r
 map_add' _ _:=by rw [map_add, mul_add, add_mul]
 map_smul' _ _:=by rw [map_smul,mul_smul_comm,smul_mul_assoc]; rfl

lemma enroof_origin(t:S.Detector):
 S.enroof t 0 0=t:=by
 ext1 f
 ext1 v
 have T (u:D): G! 0 u=u:=Subtype.ext (by rw [S.heatL_coe,S.eZero];rfl)
 change G! 0 (t f (G! 0 v))=_
 rw [T,T]


def roofing (t:𝓣) (l r:𝓛) := fun i=>S.enroof (t i) (l i) (r i)
def withWarm (Y:𝓧)(l r:𝓛) := fun i=> E! (l i) * (Y i) * E! (r i)
lemma roof_origin (t:𝓣): S.roofing t 0 0=t:=funext fun i=>S.enroof_origin (t i)
lemma roof_heat (t:𝓣)(k:𝒦)(X:𝓧)
 (b:∀i,t i=S.hatch (X i) (k i))(l r:𝓛):
 ∀i,S.roofing t l r i= S.hatch (S.withWarm X l r i) (k i):= fun i=> LinearMap.ext fun f=>by
    change G! _ * t i f * G! _=_
    rw [b,withWarm,S.hatch_heat]

variable {S} {t:Fin n→S.Detector}
lemma heated (h:toasted t)(l r:𝓛): toasted (S.roofing t l r):=by
 choose k X t' using h
 exact fun i=>⟨_,_,S.roof_heat t k X t' l r i⟩

def cortege (h:toasted t)(l r:𝓛): S.Invitation n:=garland (heated h l r)
lemma cortege_on (h:toasted t)(l r:𝓛): S.Invites (S.roofing t l r) (cortege h l r):=
 garland_on _

lemma cortege_base (h:toasted t): S.Invites t (cortege h 0 0):=by
 have q:=cortege_on h 0 0
 rwa [S.roof_origin] at q


lemma cortege_coach (h:toasted t) (l r:𝓛)
  {k:𝒦}{X:𝓧}(e:∀i,t i=S.hatch (X i) (k i)):
   cortege h l r=S.coaches k (S.withWarm X l r):=
 (cortege_on h .. |>.unique (inviting _ _ (S.roof_heat _ _ _ e l r)))

/-- Exact independence of dials, convergence at any zero prices. -/
lemma cortege_removes (h:toasted t) {d e:ℕ→Fin n→ℝ≥0}{l r:𝓛}
 (w: Tendsto d atTop (𝓝 l))(u:Tendsto e atTop (𝓝 r))
 {V:ℕ→Joint n}{F:Joint n}(p:Tendsto V atTop (𝓝 F)):
 S.Surges atTop (fun i=> cortege h (d i) (e i) (V i)) (cortege h l r F):=by
 have h':toasted t:=h
 choose k X b using h'
 simp_rw [fun L R' =>cortege_coach h L R' b]
 exact S.coaches_surge
     (fun j=> ((Gleams.warm S (tendsto_pi_nhds.mp w j)).mul (Gleams.const (X j))).mul
                    (Gleams.warm S (tendsto_pi_nhds.mp u j))) _ p

def fleet (S:Semigroup H a)(Q:𝓠)(l r:𝓛):= fun i=> S.insulate (Q i) (l i) (r i)




variable {Q:Fin n→ℝ≥0→H.Op}
def openAir (l:Fin n→ℝ≥0):Prop:=∀i,0<l i

lemma cortege_fleet (h:toasted t)(b:∀i,S.Instates (Q i) (t i))
   {l r:𝓛}(u:openAir l)(v:openAir r):
    cortege h l r = S.banners (S.fleet Q l r):=by
 have e:(fun i=>S.labelled (S.fleet Q l r i))= S.roofing t l r:=
    funext fun i=> LinearMap.ext ((b i).either_pad (u i) (v i))
 have p:=S.banner_invites (S.fleet Q l r)
 rw [e] at p; exact (cortege_on h l r).unique p
#print axioms cortege_removes
#print axioms cortege_fleet

