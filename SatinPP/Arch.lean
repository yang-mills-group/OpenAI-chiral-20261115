import SatinPP.Welts

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option maxRecDepth 4500
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Aria
open Hierarchy.Celeritas Land Hierarchy.Seld.Leal
variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ" j:max => P.advocate 3 x j
local notation "K₁" j:max => P.ManyF j (P.advocate 3 x j)
local notation "Π'" j:max=>P.wealth j (P.advocate 3 x j)
local notation "Sh"=>Shrine (P.houses x)
local notation "W"=>P.socials x
local notation "ω"=>P.lights x

open Silk Hierarchy.Seld Boundary Probe Quays SatinJets Set Breve
variable (j:Axis)

local notation "E"=>P.socials x j
local notation "C"=>P.Cathedral x
abbrev Cue:= Test4→Bench (E)→ₗ[ℂ]Bench (E)
def Lit (F:P.Cue x j):Prop:=
  ∀g:Test4,∃ (h:Test4)(m:ℕ)(T:Sh),tsupport h⊆tsupport g ∧ T.t=0 ∧
     T∈Magic W C m∧ F g=ℑ (E) (T.f j) h m

variable {P x}{A:ℕ→P.Apron}{B:ℝ}{D:P.Concert x}
   (z:P.ConcertPlays x A B D)(l:List Axis)

local notation "G"=>P.seats j x
local notation "Ξ"=>P.seats j x (D j l)
local notation "pays"=>feature (E)
include z
lemma luster : P.Lit x j (pays (Ξ)):=by
 obtain ⟨T,k⟩:=card_moons z l
 exact fun g=>⟨g,_,T,Subset.refl _,k.thin,k.buys,
    feature_eq (k.centered j) g⟩
lemma luster' : P.Lit x j (pays (Turn Ξ)):=by
 obtain ⟨T,k⟩:=card_moons z (j::l)
 have u:Silk.Role (E) 6 (Turn Ξ) (T.f j):=by
   constructor;intro v r h t
   unfold Turn seats
   rw [←P.seating_star,←z.mirrors j l h t]
   exact (k.centered j).wear v r h t
 exact fun g=>⟨g,_,T,Subset.refl _,k.thin,k.buys, feature_eq u g⟩


lemma ceiling_light (c:ℂ)(q:Prism):
   P.Lit x j (pays (surfaces (E) q (c • Ξ))) ∧
   P.Lit x j (pays (Turn (surfaces (E) q (c • Ξ)))):=by
 have h:Sold (E) Ξ:=⟨_,_,P.seats_paid j x (z.paid j l)⟩
 constructor
 · intro g;obtain ⟨f,m,T,p,u,v,a⟩:=luster j z l (sectionals j q c g)
   exact ⟨f,m,T,p.trans (sectional_tsupp _ _ _),u,v,(feature_surfaces h q c g).trans a⟩
 intro g;obtain ⟨f,m,T,p,u,v,a⟩:=luster' j z l (nextFacing j q c g)
 exact ⟨f,m,T,p.trans (facing_tsupp _ _ _),u,v,(feature_earlier h q c g).trans a⟩
#print axioms ceiling_light

omit z
variable {w:Lead.Clan→Prism}{V:∀j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)}
         {Y:Lead.Clan→Spool (P.ManyF 3 (P.advocate 3 x 3))}
   (r:P.Played x w V D A Y)
-- both actual unpadded fields. supports unrestricted
local notation "e3"=>P.seasons 3 (P.advocate 3 x 3)
include r in
lemma fully_bright(a:Lead.Clan):
   P.Lit x 3 ((Y a).Mink (e3)) ∧
   P.Lit x 3 ((Y a).dual.Mink (e3)):=by
   obtain ⟨b,t,_⟩:=r.m.seed
   have h:P.Lit x 3 (feature (e3) (P.headliner x D w a)) ∧
       P.Lit x 3 (feature (e3) (Turn (P.headliner x D w a))):=
     ceiling_light 3 t [] _ (w a)
   exact ⟨fun g=>by
      obtain ⟨f,m,T,z,p,y,v⟩:=h.1 g
      exact ⟨f,m,T,z,p,y,(feature_eq (r.tick a) g).symm.trans v⟩,fun g=>by
      obtain ⟨f,m,T,z,p,y,v⟩:=h.2 g
      exact ⟨f,m,T,z,p,y,(feature_eq (Silk.Role.turn (r.tick a)) g).symm.trans v⟩⟩


/-- supports in spacelike separation *by a lattice axis test*. -/
structure Wing (j i:Axis)(f g:Test4) :Prop where
  rooms:∃V:ℝ,∀p∈tsupport g,p i≤ V
  cost:∃s δ:ℝ≥0,0<s∧0<δ∧
       ∀p∈tsupport f,∀q∈tsupport g,|q j-p j|<(s:ℝ)∧ (s:ℝ)+δ≤q i-p i
lemma privacy {j i:Axis}{F G':P.Cue x j}{f g:Test4}
   (r:P.Ellis 3 x)(a:P.Lit x j F)(b:P.Lit x j G')
   (n:i≠j)(h:P.DayStar x j)(v:P.DayStar x i)
   (w:Wing j i f g):
 (F f).comp (G' g)=(G' g).comp (F f):=by
 obtain ⟨⟨r',l⟩,s,δ,u,y,z⟩:=w
 obtain ⟨f',m,T,t,k,c,o⟩:=a f
 obtain ⟨g',N,U,p,d,e,H⟩:=b g
 rw [o,H]
 refine esteem W ω j i T U m N (P.Cathedral x) (P.procession_LocalFieldBounds x j i r n h v)
    ⟨c,e,(k▸rfl),(d▸rfl)⟩
    g' f' s δ u y r' (fun q a=>l q (p a)) ?_
 intro q a g k'
 obtain ⟨u,v⟩:=z q (t a) g (p k')
 rw [k,d]; simpa using And.intro u v
#print axioms privacy
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
