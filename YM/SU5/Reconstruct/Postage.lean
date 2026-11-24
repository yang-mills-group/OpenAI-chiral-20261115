import YM.SU5.Reconstruct.Domain
set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 620000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Tapestry Tapestry.Altitude PhaseChoice
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
open Tower.Selected Set MeshClock Tapestry.Exhibition
open SelectionAnalysis Vacancy.Average
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  {L:Rack Λ l}{B:Clay Λ l}{T:ℕ→ℕ→Tariff}{t:ℕ→Tariff}(D:Fashion Y H i k I E L B T t)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
local notation "Dₚ" => D.toExhibition
local notation "V" => D.univ_
local notation "Q" => G.history
local notation "Qt" => G.clipped
local notation "χ" => Dome (tent Y H)
local notation "O" => Altitude.Cloud (Dome (tent Y H))
local notation "P₀" s:max => vistaFinish Y H s (Dₚ)

section postage
variable (Λ:Preparation) (n u:ℕ)
local notation "M"=> timeMesh Λ
local notation "p₀" v:max=> placement v
/-- grid and its real displacement in our physical units -/
def meshPos (n:ℕ): Cover→+placement Λ where
  toFun v j:=notch M n (v j)
  map_zero' := funext fun j=> notch_zero ..
  map_add' x y:=funext fun j=> notch_add ..
def physPos : placement Λ→+ RSpace where
  toFun v j:=(v j).val
  map_zero' :=rfl
  map_add' _ _:=rfl
def netcast (n u:ℕ)(v:Cover):Cover:= fun j=>castor M n u (v j)
local notation "m₀" k:max=> meshPos Λ k
local notation "X₀"=>physPos Λ
lemma netcast_up (h:n ≤ u) (v:Cover) : (m₀ u) (netcast Λ n u v)=(m₀ n) v := funext fun i=> notch_up M n u h _
lemma meshpos_inj : Injective (meshPos Λ n) := fun _ _ h=> funext fun i=> notch_tight M n (congrFun h i)
lemma real_pos : Continuous (physPos Λ) := continuous_pi fun i=> continuous_subtype_val.comp (continuous_apply i)
lemma everywhere_pos : DenseRange (physPos Λ) := DenseRange.piMap fun i:Axis=> (daylight M).denseRange_val -- check
lemma calibrated_step (a:ℤ) : bell (timeMesh Λ) n a= glint Λ n (Heat.gaugeShift Λ.block (2*a)) := by
 change (a:ℝ) * (↑((8 * (Λ.block.val:ℝ≥0))/(Λ.R.L.val:ℝ≥0)^n):ℝ)= (↑(Heat.gaugeShift Λ.block (2*a)):ℝ)/(Λ.R.L.val:ℝ)^n; unfold Heat.gaugeShift; simp only [NNReal.coe_div,NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast]
 push_cast; ring
lemma scaled_notch (v:Cover)(j:Axis) : physPos Λ ((meshPos Λ n) v) j= glint Λ n (Heat.gaugeShift Λ.block (2*(v j))):= calibrated_step ..
/-- Basic region move -/
def carried (v:RSpace) (X:Set RSpace): Set RSpace := (fun x:RSpace=> v+x) '' X
lemma carried_plus (a b:RSpace)(X:Set RSpace): carried a (carried b X)=carried (a+b) X:=by
 simp only [carried,Set.image_image,add_assoc]
lemma carried_zero(X:Set RSpace) : carried 0 X=X:=by simp [carried]
lemma carried_disjoint (v:RSpace){X Z:Set RSpace}(h:Disjoint X Z): Disjoint (carried v X) (carried v Z) := by
 refine Set.disjoint_left.mpr (fun i p q=>?_); obtain ⟨a,p,rfl⟩:=p; obtain ⟨b,q,r⟩:=q; rw [(show b=a from add_left_cancel r)] at q; exact Set.disjoint_left.mp h p q
lemma sendOne (a:ℤ)(U:Set RSpace)(j:Axis) : carried (X₀ ((m₀ n) (a • step j))) U = (steer j (glint Λ n (Heat.gaugeShift Λ.block (2*a)))) '' U := by
 unfold carried; congr 1; funext x i; unfold steer; rw [Pi.add_apply,scaled_notch]
 by_cases h : i=j
 · subst i; simp [add_comm]
 simp [h,glint,gaugeShift]
end postage
local notation "m₀" k:max=> meshPos Λ k
local notation "X₀"=>physPos Λ
-- CAD extensive action using Knob at each level, now on the Dome algebra
variable (v:Cover)
local notation "Uα" j:max=>cruise j K (gaugeT K (v j))
variable (Z:List Axis)
def tour : Dome K →ₐ[ℂ] Dome K := Z.foldr (fun j b=> (cruise j (tent Y H) (gaugeT (tent Y H) (v j))).comp b) (AlgHom.id ℂ _)
local notation "f₀" t:max=>tour Y H v t
lemma tour_step (j:Axis)(t:List Axis): tour Y H v (j::t)=(Uα j).comp (f₀ t):=rfl
-- need keep strict Cov on it
lemma tour_c (x:Dome K) : (tour Y H v Z x).val=cad (tent Y H) Z v x.val:=by
 induction Z with
 | nil => rfl
 | cons j t ih=> rw [tour_step,AlgHom.comp_apply, sailsTo,cad_step,ih]; rfl
lemma tour_en {x:Dome K}(h:x∈enclave K) : (tour Y H v Z x)∈enclave K:=by
 induction Z with
 | nil => exact h
 | cons j t ih=> rw [tour_step,AlgHom.comp_apply]; exact aureoleEnclave _ _ _ (aureoleEnclave _ _ _ ih) -- order
lemma subtotal : (ordinate.map (fun i=>v i • step i)).sum=v:=by
 ext i
 suffices h:∀ (u:List Axis) (p:u.Nodup), ((u.map fun j=> v j • step j).sum:Cover) i= if i∈u then v i else 0 from (h _ ordinate_one).trans (if_pos (ordinates i))
 intro u; induction u with
 | nil=>simp
 | cons j u ih =>
   intro p; rw [List.map_cons,List.sum_cons,Pi.add_apply,ih (List.nodup_cons.mp p).2]; by_cases h : i=j
   · subst i; simp [(List.nodup_cons.mp p).1]
   simp [h]
lemma tour_packed {x: Dome K}{X:Set RSpace}{n:ℕ}(p:x∈ keep Λ l n K true (handstamp X)) : tour Y H v Z x ∈ keep Λ l n K true (handstamp (carried ((X₀) (meshPos Λ n ((Z.map (fun i=> v i • step i)).sum))) X)) := by
 induction Z with
 | nil=> simpa [carried_zero,tour] using p
 | cons i z ih=>
   rw [tour_step,AlgHom.comp_apply, List.map_cons,List.sum_cons,map_add,map_add,←carried_plus,sendOne]
   exact hand_steer i K (gaugeT K (v i)) Λ l n _ ih

def march (v:Cover) := tour Y H v ordinate
lemma travels {x: Dome K}{X:Set RSpace}{n:ℕ}(p:x∈ keep Λ l n K true (handstamp X)) : march Y H v x ∈ keep Λ l n K true (handstamp (carried (X₀ ((m₀ n) v)) X)):= by
  simpa only [march,subtotal] using tour_packed Y H v ordinate p
lemma marchOut {x:Dome K} : fieldArg Y H (march Y H v x)= relocateWorld Y H false v (fieldArg Y H x):= Subtype.ext ((tour_c Y H v _ x).trans (world_val Y H false v (fieldArg Y H x)).symm)
lemma march_ground (x:Dome K) : march Y H 0 x=x := by apply Subtype.ext; change (tour Y H 0 _ x).val=_; rw [tour_c, cad_zero _ _ x.property]
lemma march_add (z:Cover)(x:Dome K) : march Y H v (march Y H z x)=march Y H (v+z) x := by apply Subtype.ext; unfold march; rw [tour_c,tour_c,tour_c,cad_plus _ _ x.property]
include G
lemma tour_upgrade(n:ℕ)(x:Dome K) : liftD Y H n D.toExhibition (tour Y H v Z x)= tour Y H (netcast Λ n (n+1) v) Z (liftD Y H n D.toExhibition x):= by
 induction Z with
 | nil=>rfl
 | cons i z ih=>
   rw [tour_step,tour_step,AlgHom.comp_apply,AlgHom.comp_apply,←ih]
   apply Subtype.ext; let a:= tour Y H v z x
   change _= (cruise i K _ (liftD Y H n D.toExhibition a)).val
   rw [sailsTo,lifts_here Y H V G,sailsTo,lifts_here Y H V G]
   have h:= acreage_X Y H G i n 1 (F:=a.val) a.property (gaugeT K (v i))
   have hp:Λ.R.L.val*(gaugeT K (v i))= gaugeT K (netcast Λ n (n+1) v i):=by unfold netcast castor timeMesh gaugeT Heat.gaugeShift; rw [show n+1-n=1 by omega, pow_one]; ring
   -- cast?
   rw [pow_one,hp] at h; exact h
omit G
local notation "Fₚ" => vistaDressing Y H D.toExhibition
lemma retained {U:Set RSpace}{x:O}(s:ℕ)(p:x∈PolAt Y H s U): (P₀ s) x∈keep Λ l s K true (handstamp U):= crownShelter Λ l s Fₚ _ (fun i x=>rfl) _ (fun i f h=> roofline Λ l i true (handstamp U) D.toExhibition h) ((well_spec ..).mp p).1
/-- The shifted test. Use rank above all heights paid. Does not preserve pointwise
coincident products by fiat. This pins at the paying height (not literally identity),
so only up to `Concurrent`. -/
def parcelTo (n:ℕ)(v:Cover): Altitude.Cloud (Dome K) →ₗ[ℂ] Altitude.Cloud (Dome K):= (pinhole χ n).toLinearMap.comp ((march Y H v).toLinearMap.comp (vistaFinish Y H n D.toExhibition))
-- avoid Parcel name clash
local notation "â" k:max p:max => parcelTo Y H D k p
lemma parcel_mem {X:Set RSpace}(n:ℕ){x:Altitude.Cloud (Dome K)}(p:x∈ PolAt Y H n X) : parcelTo Y H D n v x∈ PolAt Y H n (carried ((X₀) ((m₀ n) v)) X):= oneSlotWell Λ K l true _ _ n (by simp) (travels Y H v (retained Y H D n p)) (tour_en Y H v _ (D.toExhibition.finishCoherent Y H n x p (inside_budget Y H p))) -- need mark algebra Tapestry deck
lemma tallied (n:ℕ)(x:O) : (P₀ n) ((â n v) x)=march Y H v ((P₀ n) x):=Decking.outcrop ..
include G in
lemma talliedUp (n u:ℕ)(p:n≤u){X:Set RSpace}{x:O}(v':x∈PolAt Y H n X): (P₀ u) ((â n v) x)= march Y H (netcast Λ n u v) ((P₀ u) x) := by
 induction u,p using Nat.le_induction with
 | base =>
    rw [tallied,show netcast Λ n n v=v from funext fun i=>by simp [netcast,castor]]
 | succ u p ih=>
    let q:= (â n v) x; let z := D.toExhibition; let a:= netcast Λ n u v
    have ht:(P₀ (u+1)) x= liftD Y H u D.toExhibition ((P₀ u) x):= Decking.joins _ _ _ _ (inside_budget Y H (polAt_up Y H p v'))
    have hz:(P₀ (u+1)) q= liftD Y H u D.toExhibition ((P₀ u) q):= Decking.joins _ _ _ _ (inside_budget Y H (polAt_up Y H p (parcel_mem Y H D v n v')))
    have hw: netcast Λ u (u+1) a=netcast Λ n (u+1) v:= meshpos_inj Λ (u+1) (Eq.trans (netcast_up _ _ _ (by omega) _) ((netcast_up Λ n u p v).trans (netcast_up Λ n _ (by omega) v).symm))
    rw [ht]; change (P₀ (u+1)) q= _; rw [hz,←hw]; unfold q; rw [ih]; exact tour_upgrade Y H D G a _ _ _
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
