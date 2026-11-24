import YM.SU5.FiniteGaugeData.Tapestry.Arch
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 480000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale FullBill

/-!
# B maps of the elected course. Presentation independent, defined with their
own support radius claims, connected to the Family readers. Note the exact
form of multiplicativity that is claimed---on *separated* marks for this one
step. (Plus reflection). This allows feeding products INTO the interlevel maps
without using any assumption that they're global Algebra maps, positive or even
arising from a common Printed history in the thermodynamic limit.
-/
set_option quotPrecheck false
section
variable (K:Calibration)
variable (S T:Finset Cover) (u v: Dome K)
lemma coAwake : ∃ S:Finset Cover, u∈bay K S true ∧ v∈bay K S true:=
 ⟨precinct K u ∪ precinct K v,tallerBay K _ _ subset_union_left (precinct_spec K u),tallerBay K _ _ subset_union_right (precinct_spec K v)⟩
lemma coCertain : ∃ (S:Finset Cover) (x y : Swatch S), u=badge K S x ∧ v=badge K S y:=by
 obtain ⟨S,s,t⟩:= coAwake K u v; exact ⟨S,_,_, (trophy_at K u s).symm, (trophy_at K v t).symm⟩
end

open Heat -- gaugeShift
variable {Λ: Preparation} {l : ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H:Real.exp 1 ≤ Λ.x)
variable (s i k:ℕ)(S R:Finset Cover)
local notation "M" => tent Y H
local notation "U"=> Dome (M)
local notation "σ" => side Y i s
local notation "sUp" S:max => followBox (Λ:=Λ) (l:=l) S

-- native dress. no Pay necessary for defining this algebra map.
lemma safeNat (x: Dome (tent Y H)):AtSupport false univ (exhibit Y H s i x.val):=by
 obtain ⟨S,h⟩:= findsBay (tent Y H) x; exact (exhibited _ _ _ _ S ((locates ..).1 h)).mono (subset_univ _)
def rovingₗ : Dome (tent Y H)→ₗ[ℂ] Ward (side Y i s) where
 toFun x:=frock (safeNat Y H s i x)
 map_add' u v:= attireL_inj (map_add (exhibit ..) u.val v.val)
 map_smul' a u:= attireL_inj (map_smul (exhibit ..) a u.val)
def roving : Dome (tent Y H) →ₐ[ℂ] Ward (side Y i s) := AlgHom.ofLinearMap (rovingₗ Y H s i) (attireL_inj (actual_one ..)) fun i j=> attireL_inj (actual_product ..)
lemma roamsAttire (x): attire (roving Y H s i x)= exhibit Y H s i x.val := rfl
@[simp] lemma rovingBadge (x:Swatch S): roving Y H s i (badge (tent Y H) S x)= wearStep Y H S s i x:= attireL_inj rfl
lemma roams : Surjective (roving Y H s i):=by intro x; obtain ⟨v,rfl⟩:= wardrobeRange Y H s i x; exact ⟨_,rovingBadge Y H s i _ v⟩
lemma usesSharp (x) (p: Pay Y s i k): savings Y s i k (roving Y H s i x)= Journey.sharp Y H s i k x.val:= (trueSavings Y s i k _ p).trans (actualRead Y H s i k x.val).symm
lemma firstAppearance {x:Dome M}(p:x∈vestibule M false): ∃ f: Window.Evaluation (side Y i s),attire (roving Y H s i x)=toMark f∧Continuous f:=by
  obtain ⟨v,h,e⟩:= concentration (tent Y H) p (momentm Y i s); exact north (side Y i s) (terrain Y H (Y.ir i) s) v e h
where north{P:Side}(n:Side)(h:P=n)(v:Window.Evaluation P)(e:Continuous v){u:Mark P}(z:u=toMark v):∃ f:Window.Evaluation n, arrange P n h u=toMark f∧ Continuous f:= by subst n; exact ⟨v,z,e⟩
lemma paidEnclave {x:Dome M}(p:x∈enclave M): covariant (attire (roving Y H s i x)):= validate (Y:=Y) (s:=s) (i:=i) H p -- tune

variable {a b:ℕ→ℕ} {I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ} {L:Rack Λ l}{B:Clay Λ l} (D:Exhibition Y H a b I E L B)
namespace Exhibition
lemma refreshed (u:Dome (tent Y H)):
    refreshments Y H s i D (roving Y H s i u)= I s u.val i:=by
 obtain ⟨S,h⟩:= findsBay (tent Y H) u; obtain ⟨x,rfl⟩:= accolade (tent Y H) S u h; rw [rovingBadge,←ContinuousLinearMap.comp_apply,Exhibition.bonusBalance]; rfl
include D
local notation "up" => badge (tent Y H)
local notation "sμ" => refresh -- no
lemma compatBuild (u:Dome M): ∃ w:Dome (tent Y H),∀ (S:Finset Cover)(x: Swatch S),badge (tent Y H) S x=u→ w=badge (tent Y H) (sUp S) (B S s x):=by
  obtain ⟨S,h⟩:=findsBay (tent Y H) u; obtain ⟨x,rfl⟩:= accolade (tent Y H) S u h; exact ⟨badge (tent Y H) (followBox (Λ:=Λ) (l:=l) S) (B S s x),fun T y e=> Subtype.ext (D.overlap Y H S T s (show render S (M) x=render T (M) y from congrArg Subtype.val e.symm))⟩
local notation "ζ" => compatBuild Y H s D
noncomputable def plaster (u:Dome M): Dome M:= (ζ u).choose
lemma built (v:Swatch S): plaster Y H s D (up S v)= up (sUp S) (B S s v):= (ζ (up S v)).choose_spec S v rfl

def liftD : Dome (tent Y H) →ₗ[ℂ] Dome (tent Y H) where
 toFun:= plaster Y H s D
 map_add' u v:=by obtain ⟨S,x,y,rfl,rfl⟩:= coCertain (tent Y H) u v; rw [← map_add,built,built,built,map_add,map_add]
 map_smul' z x:= by obtain ⟨S,h⟩:= findsBay (tent Y H) x; obtain ⟨f,rfl⟩:= accolade (tent Y H) S x h; rw [← map_smul,built,built,map_smul,map_smul]; rfl
lemma fromLocal (x:Swatch S) : (liftD Y H s D) (up S x)=up (sUp S) (B S s x):= D.built Y H s S x
lemma risePay {f:Dome M} (h:f∈bay M S true): liftD Y H s D f∈bay M (followBox (Λ:=Λ) (l:=l) S) true:=by obtain ⟨x,rfl⟩:= accolade (tent Y H) S f h; rw [fromLocal]; exact locatesBadge ..
lemma riseGauge {f:Dome M} (h:f∈enclave M) : liftD Y H s D f∈enclave M:=by
 obtain ⟨S,h'⟩:=findsBay (tent Y H) f; obtain ⟨x,rfl⟩:= accolade (tent Y H) S f h'; rw [fromLocal]; exact remainsNeutral S Y H D s x h
lemma onePlaster : liftD Y H s D 1=1:= by rw [←laureled (tent Y H) ∅,fromLocal,D.unit_preserved Y H]; simp
lemma Breflect (f:Dome M)(α:Axis)(z:ℤ): liftD Y H s D (aureole M α z f)= aureole M α (Scaled Λ z) (liftD Y H s D f):=by
 obtain ⟨S,h⟩:= findsBay (tent Y H) f; obtain ⟨x,rfl⟩:= accolade (tent Y H) S f h; rw [aureoleReflect,fromLocal,fromLocal]; exact Subtype.ext (D.interlevel_reflect Y H S s x α z)
lemma Bseparated {f g:Dome (tent Y H)} (p:f∈bay M S true)(q:g∈bay M R true)(v:∀ᶠ i:ℕ in atTop,∀ x∈region S (side Y i s),∀ z∈ region R (side Y i s), 2*(Advance.nearZero (aliasLaw Λ)+distanceLaw l)<separation x z): liftD Y H s D (f*g)= liftD Y H s D f * liftD Y H s D g:=by
 obtain ⟨x,rfl⟩:= accolade (tent Y H) S f p; obtain ⟨y,rfl⟩:= accolade (tent Y H) R g q
 obtain ⟨T,h⟩:= findsBay (tent Y H) (badge (tent Y H) S x*badge (tent Y H) R y); obtain ⟨z,h⟩:= accolade (tent Y H) T _ h
 rw [←h,fromLocal,fromLocal,fromLocal]; exact Subtype.ext (D.interlevel_mul Y H S R s (R:=T) (f:=x) (g:=y) (z:=z) (congrArg Subtype.val h) v)

def planet : Dome (tent Y H)→ₗ[ℂ]ℂ where
 toFun x:= E s x.val
 map_add' u v:=by
   obtain ⟨S,x,y,rfl,rfl⟩:= coCertain (tent Y H) u v; rw [←map_add]; exact map_add (thermodynamic Y H S s D) x y
 map_smul' z x:=by
   obtain ⟨S,h⟩:= findsBay (tent Y H) x; obtain ⟨f,rfl⟩:= accolade (tent Y H) S x h; rw [←map_smul]; exact map_smul (thermodynamic Y H S s D) z f
lemma planetE (f): planet Y H s D f=E s f.val:=rfl
lemma localThermo (x:Swatch S): planet Y H s D (badge (tent Y H) S x)=thermodynamic Y H S s D x:=rfl
lemma planetTravel(f): planet Y H s D f= planet Y H (s+1) D (liftD Y H s D f):=by obtain ⟨S,s⟩:=findsBay (tent Y H) f; obtain ⟨x,rfl⟩:= accolade (tent Y H) S f s; rw [fromLocal]; exact D.exactFamily Y H S _ x -- rename shadow
lemma periodPitch (x): Tendsto (fun v:ℕ=> refreshments Y H s (a v) D (roving Y H s (a v) x)) atTop (𝓝 (planet Y H s D x)):=by
  simp_rw [refreshed]; exact (D.univ_.together s x.val x.property).periods
lemma planet1 : planet Y H s D 1=1:=tendsto_nhds_unique_of_eventuallyEq (periodPitch Y H s D 1) tendsto_const_nhds (Eventually.of_forall fun i:ℕ=> by dsimp only; rw [map_one,savingsUnit])
end Exhibition
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.paidEnclave
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Exhibition.Bseparated
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Exhibition.planetTravel
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Exhibition.Breflect
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Exhibition.planet1
