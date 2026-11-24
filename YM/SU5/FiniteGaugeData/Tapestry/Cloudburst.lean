import YM.SU5.FiniteGaugeData.Tapestry.Frosted
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 440000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale FullBill
open Nacre Mir Phase RP
open Altitude Heat
open PiTensorProduct (tprod)

/-!
# Gauge group of the resolution hierarchy. We require invariance under ALL
spacetime vertex choices `$\prod_{x \in grids} SU(5)$`. There is no continuity restriction. Easier to
represent via restrictions of point maps on RSpace. This is equivalent to
choosing an arbitrary gauge on the resolution grid, being coherent (common
coarsening = same values). We perform the gauge actions on the *tests*, not
on projective Hilbert-space GNS values. Even matrix probes can use both
links; both must be transformed simultaneously. Physical first-link-only reads
are identified by `false`. In either case, advancement of a test is in the wide
algebra regardless of whether one restricts the desired physical *questions*.
-/
set_option quotPrecheck false
variable (Λ: Preparation) (K:Calibration)

abbrev GPhysical := RSpace→ SU.E
def addressG (n:ℕ)(x:Cover): RSpace:= fun i=> markZ Λ n (x i)
variable {K} (n:ℕ) (u v:GPhysical)
local notation "Z" x:max=> Λ.R.L.val • (x:Cover)
abbrev restrictG : Cover → SU.E:= u∘(addressG Λ n)
lemma address_inj : Injective (addressG Λ n):=fun f g h=> funext fun i=> by
  have hx: ((f i:ℤ):ℝ) / precisionAt Λ n=((g i:ℤ):ℝ) / precisionAt Λ n:= congrFun h i
  exact_mod_cast div_left_inj' (positiveScale Λ n).ne'|>.mp hx -- check name
lemma addressUp (x:Cover): addressG Λ (n+1) (Z x)=addressG Λ n x:= by
  funext i; have h:(Λ.R.L.val • x) i=Scaled Λ (x i):=by unfold Scaled; rw [Pi.smul_apply,nsmul_eq_mul]; -- maybe by definition
  unfold addressG; rw [h,markUp]
lemma gaugeHarmony: restrictG Λ n u=parentGauge Λ (restrictG Λ (n+1) u):= funext fun i=> congrArg u (addressUp Λ n i).symm
lemma iceExtension (T: Cover→ SU.E): ∃ x:GPhysical, restrictG Λ n x=T:= ⟨Function.extend (addressG Λ n) T 1,Function.extend_comp (address_inj Λ n) _ _ ⟩
lemma allCoherent (T:ℕ→ GVertex)(p:∀ i, T i=parentGauge Λ (T (i+1))): ∃ x:GPhysical, T=fun n=> restrictG Λ n x:=by
  suffices h : ∀ i j a b,addressG Λ i a=addressG Λ j b → T i a=T j b by
    let v (u:RSpace):Prop:=∃ i:ℕ × Cover,addressG Λ i.1 i.2=u
    let f:GPhysical:=fun u=> if p:v u then T (Classical.choose p).1 (Classical.choose p).2 else 1
    refine ⟨f,?_ ⟩; funext n x; change T n x=f (addressG Λ n x); unfold f; let y:= addressG Λ n x; let u:v y:= ⟨(n,x),rfl⟩; rw [dif_pos u]; exact h _ _ _ _ (Classical.choose_spec u).symm
  have e : ∀ a:Cover,∀ i j:ℕ,i≤j→ ∃ b:Cover,addressG Λ j b=addressG Λ i a∧ T j b=T i a:=by
    intro a i j h; induction j,h using Nat.le_induction with
    | base=> exact ⟨a,rfl,rfl⟩
    | succ j u ih=> obtain ⟨b,h,g⟩:= ih; exact ⟨Z b,(addressUp Λ j b).trans h,(congrFun (p j).symm b).trans g⟩
  intro i j a b h; obtain ⟨u,U,X⟩:= e a i (max i j) (le_max_left ..); obtain ⟨v,h',Q⟩:=e b j (max i j) (le_max_right ..); rw [←X,← Q,address_inj Λ (max i j) (U.trans (h.trans h'.symm))]

lemma deflectPoint (a:Axis)(z:Sunlight Λ)(p:z.start ≤ n)(x:Cover):
    addressG Λ n ((plane a (z.marks n)).motion x)=mirrorE a (z.hinge Λ) (addressG Λ n x):=by
 funext i; unfold addressG mirrorE; rw [fling_move,← z.home Λ n p]; by_cases h:a=i
 · rw [if_pos h, if_pos h.symm]; unfold markZ; push_cast; ring
 rw [if_neg h,if_neg (Ne.symm h)]
lemma gaugeReflection (a:Axis)(z:Sunlight Λ)(p:z.start ≤ n): restrictG Λ n (u∘ mirrorE a (z.hinge Λ))=reflectGauge a (z.marks n) (restrictG Λ n u):= funext fun x=>congrArg u (deflectPoint Λ n a z p x).symm

variable (K)
-- whole test-space action. right action.
def rainyTail (f:ℕ→Dome K): ℕ→Dome K:= fun i=> pennant K (restrictG Λ i u) (f i)
local notation "o"=>fun i=> (pennant K (restrictG Λ i u)).toLinearMap
def rainfall : Cloud (Dome K) →ₐ[ℂ] Cloud (Dome K):= AlgHom.ofLinearMap (plume (fun i=> (pennant K (restrictG Λ i u)).toLinearMap)) (plumeUnit _ (fun i=>map_one (pennant K (restrictG Λ i u)))) (plumeTimes _ (fun i x y=> map_mul (pennant K (restrictG Λ i u)) x y))
lemma rainfallPure (x): rainfall Λ K u (pureShot K x)=pureShot K (rainyTail Λ K u x):= pluage .. -- order u K? binder K earlier or here?
lemma rainTurns (x): rainfall Λ K v (rainfall Λ K u x)=rainfall Λ K (u*v) x:=by
  induction x using PiTensorProduct.induction_on with
  | add x y h p=> rw [map_add,map_add,h,p,map_add]
  | smul_tprod r y=>
    change rainfall Λ K v (rainfall Λ K u (r • pureShot K y))=_; rw [map_smul,map_smul,map_smul,rainfallPure,rainfallPure]; change _ = _ • rainfall Λ K _ (pureShot K y); rw [rainfallPure]; exact congrArg (fun x=> r • pureShot K x) (funext fun x=> pennantCompose K _ _ (y x))
lemma rainingOne(x): rainfall Λ K 1 x=x:=by
  induction x using PiTensorProduct.induction_on with
  | add x y h p=> rw [map_add,h,p]
  | smul_tprod r y=>
    change rainfall Λ K (1:GPhysical) (r • pureShot K y)=_; rw [map_smul,rainfallPure]; exact congrArg (fun x=>r • pureShot K x) (funext fun i=> show pennant K 1 _=_ from pennantId K (y i))
lemma rainyEnough {x: ℕ → Dome K}(p:Enough n x): Enough n (rainyTail Λ K u x):= plumeEnough (χ:=RingHom.id ℂ) (A:=Dome K) (fun i=> (pennant K (restrictG Λ i u)).toLinearMap) (fun i=>map_one (pennant K (restrictG Λ i u))) p -- argument order?
lemma raining_height{x}(p:x∈shorter (Dome K) n): rainfall Λ K u x∈shorter (Dome K) n:= plumeCut _ (A:=Dome K) (χ:=RingHom.id ℂ) (fun i=>map_one (pennant K (restrictG Λ i u))) n p
lemma gaugesSlot (x:Dome K) : rainfall Λ K u (pinhole _ n x)=pinhole _ n (pennant K (restrictG Λ n u) x):=by
  rw [pinhole_apply,pinhole_apply]; change rainfall Λ K u (pureShot K _)=_; rw [rainfallPure]; apply congrArg (pureShot K); funext i; by_cases h:i=n
  · rw [h,rainyTail,update_self,update_self]
  rw [rainyTail,update_of_ne h,update_of_ne h, map_one]
variable (l:ℕ)(S:Set ℕ)(V:Set RSpace)(wide:Bool)
lemma rainfallOwned {x:Dome K} (p:x∈keep Λ l n K wide V):
    pennant K (restrictG Λ n u) x∈keep Λ l n K wide V:=by obtain ⟨X,t,v⟩:=p; exact ⟨X,pennantLocal K X _ t,v⟩
lemma rainfallKeeps {x:Cloud (Dome K)} (p:x∈jetty Λ l K wide V S): rainfall Λ K u x∈ jetty Λ l K wide V S:=by
 change Altitude.plume (fun i=> (pennant K (restrictG Λ i u)).toLinearMap) x∈ _; refine plumeExtend (fun i=> (pennant K (restrictG Λ i u)).toLinearMap) (P:={f|Officer S (fun i=>keep Λ l i K wide V) f}) (Q:={f|Officer S (fun i=>keep Λ l i K wide V) f}) (fun f (h:Officer _ _ f)=>?_) p
 change Officer _ _ (rainyTail Λ K u f); exact ⟨⟨h.toll.choose,rainyEnough Λ K h.toll.choose u h.toll.choose_spec⟩,fun i=> rainfallOwned Λ K i u l V wide (h.observes i),fun i v=> by rw [rainyTail,h.forbids i v,map_one]⟩
lemma rainReflect {x:Cloud (Dome K)}(z:Sunlight Λ)(a:Axis)(t:S ⊆ z.arena Λ)(p:x∈ jetty Λ l K wide V S): rainfall Λ K u (z.oppose Λ a K x)= z.oppose Λ a K (rainfall Λ K (u∘ mirrorE a (z.hinge Λ)) x):=by
 let G:= u∘mirrorE a (z.hinge Λ)
 apply boarded (P:={f| Officer S (fun i=>keep Λ l i K wide V) f}) (M:=fun x=>rainfall Λ K u (z.oppose Λ a K x)= z.oppose Λ a K (rainfall Λ K G x)) ?_ ?_ ?_ ?_ p
 · intro f (h:Officer _ _ f); change rainfall Λ K u (z.oppose Λ a K (pureShot K f))=z.oppose Λ a K (rainfall Λ K G (pureShot K f)); rw [Sunlight.opposes,rainfallPure,rainfallPure, Sunlight.opposes]; apply congrArg; funext i; by_cases q:z.start ≤ i
   · change pennant K _ (aureole K _ _ _) = aureole K _ _ (pennant _ (restrictG Λ i G) _); unfold G; rw [pennantReflect, gaugeReflection Λ i u a z q] -- V order
   rw [rainyTail, Sunlight.opponent,Sunlight.opponent,plumeTail,plumeTail,rainyTail,h.forbids i (fun p=>q (t p)),aureoleUnit,map_one,map_one,aureoleUnit]
 · simp
 · intro x y p q h v; rw [map_add,map_add,h,v,map_add,map_add]
 intro z x e k; rw [LinearMap.map_smulₛₗ, map_smul,k,map_smul,LinearMap.map_smulₛₗ]
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.rainReflect
#print axioms YM.CF.Buffered.Afterglow.Tapestry.rainTurns
#print axioms YM.CF.Buffered.Afterglow.Tapestry.rainfallKeeps
#print axioms YM.CF.Buffered.Afterglow.Tapestry.allCoherent
