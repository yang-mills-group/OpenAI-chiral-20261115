import YM.SU5.CompassRose.Pier

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 500000
set_option quotPrecheck false
set_option linter.unusedSectionVars false

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine Preparation.Yoke
open CF.Velvet CF.Pannier.Chancel CF.Pannier.Chancel.Rous Pressure
open YM.Stationary (Gaia)
open Onyx Regis.Circuit Regis.Head Regis.Head.Brecht Exterior Hiro

namespace Rose
open EmberWind Jewel
open CF.Fir CF.Jill CF.Flare CF.Kea CF.Emu CF.Dial Lamour Lamour.Bridge Cache Glaze Next.Free Laurent
open WakeInvestment Gleam Gleam.Wake Regis.Head.Brecht
variable (P : Spine)(v : ℕ→ℕ)(β : ℕ→ℝ) (T : Pools P v β)
local notation "pᵥ" z:max => Rose.period P (v ((z:ℕ×ℕ).2))
local notation "cᵥ" z:max => Rose.cutoff P (v ((z:ℕ×ℕ).2))
local notation "O" z:max => orbitSize P v z
local notation "Y" => P.run
local notation "R" s:max A:max => sPow P.par s A
local notation "Zy" s:max A:max => zoomR P.par A s
variable {A:ℝ} (p:0<A)
local notation "Ω" z:max => (Y).uv (cᵥ z) - ((z:ℕ×ℕ).1)
local notation "B₀" z:max => P.par.V.L.mood (Ω z)
local notation "G₀" z:max => P.par.V.L.tied (Ω z)
local notation "φ" z:max => grid P v z
local notation "μZ" z:max => stdGaussian (φ z)
local notation "χ₀" z:max => reachCost Y ((z:ℕ×ℕ).1) (pᵥ z) (cᵥ z) (κFix β ((z:ℕ×ℕ).1))
variable {I:Type*} (W:I→ℕ→Staff)

-- specialize discrete polynomial cost to color*two spin tags and pay the entire read (not
-- compressed products). Can sum AFTER taking full Wick contractions. A piece multiplies
-- atom colorEntry(a,b), and the actual ordered `ton` twice.
abbrev Blot := SU.group.ColorIndex × (SU.Slot × SU.Slot)
abbrev Ball (I:Type*) := I × Blot
abbrev pigment (i:Blot) : ℂ:=colorEntry i.2.1 i.2.2 (mug i.1)
abbrev panelColor (i:Ball I) : CTag I := (i.1,i.2.1)
def charge (l:List (Ball I)) : ℂ:=(l.map fun i=> pigment i.2).prod
def legs (i:Ball I) : List (sIndex I) := [(i.1,i.2.2.2,true),(i.1,i.2.2.1,false)]
abbrev stream (V:List (Ball I)) := V.flatMap legs

def deposits {G:Type*}[AddCommMonoid G](L : List I)(t : List (Ball I)→G): G:= match L with
  | []=> t []
  | i::l=> ∑ b:Blot,deposits l (fun u=> t ((i,b)::u))
section algebra
variable {G K X: Type*} (L:List I)
lemma invest_sum [AddCommMonoid G] [AddCommMonoid K] (f:List (Ball I)→G)(u:G →+ K) : u (deposits L f)=deposits L (fun x=>u (f x)):=by induction L generalizing f with|nil=>rfl|cons i l p=> rw [deposits,deposits,map_sum]; exact sum_congr rfl fun _ _=> p _
lemma invest_dep [AddCommMonoid G](f g:List (Ball I)→G)(t:∀ l,l.map Prod.fst=L→ f l=g l):deposits L f=deposits L g:=by
 induction L generalizing f g with
 | nil=> exact t _ rfl
 | cons i l p=> exact sum_congr rfl fun v _=> p (fun o=> f ((i,v)::o)) _ (fun i u=>t _ (by simp only [List.map_cons,u]))
lemma invest_limit [TopologicalSpace G] [AddCommMonoid G] [ContinuousAdd G](u:Filter X)(f:List (Ball I)→X→G)(F:List (Ball I)→G) (t:∀ l,l.map Prod.fst=L→ Tendsto (f l) u (𝓝 (F l))) : Tendsto (fun i=> deposits L (fun x=>f x i)) u (𝓝 (deposits L F)) := by
 induction L generalizing f F with
 | nil=>exact t _ rfl
 | cons i l p=> exact tendsto_finsetSum univ fun v _=> p (fun x=> f ((i,v)::x)) _ (fun i u=> t _ (by simp only [List.map_cons,u]))
lemma invest_mul [Semiring G](f:Ball I→G): (L.map (fun i=> ∑ b:Blot, f (i,b))).prod=deposits L (fun t=> (t.map f).prod):=by
 induction L with
 | nil=>rfl
 | cons i l p=>
   rw [List.map_cons,List.prod_cons,deposits,p,sum_mul]; apply sum_congr rfl; intro v _; exact invest_sum l _ (AddMonoidHom.mulLeft (f (i,v)))
variable {X' : Type*} [MeasurableSpace X'] {μ:Measure X'}
lemma invest_integrable (f:List (Ball I)→X'→ℂ)(g:∀ t,t.map Prod.fst=L → Integrable (f t) μ) : Integrable (fun y=> deposits L (fun x=> f x y)) μ:=by induction L generalizing f with|nil=> exact g [] rfl | cons i l p=> exact integrable_finsetSum _ (fun v _=> p (fun x=> f ((i,v)::x)) fun x h=>g _ (by simp only [List.map_cons,h]))
lemma invest_integral (f:List (Ball I)→X'→ℂ)(g:∀ t,t.map Prod.fst=L → Integrable (f t) μ) : (∫ y, deposits L (fun x=> f x y)∂μ)=deposits L fun x=> ∫ y,f x y ∂μ :=by
 induction L generalizing f with
 | nil=>rfl
 | cons i l ih=>
   have he(v:Blot): ∀ t,t.map Prod.fst=l → Integrable (f ((i,v)::t)) μ:=fun t h=> g _ (by simp only [List.map_cons,h]);
   simp_rw [deposits]; rw [integral_finsetSum]; · exact sum_congr rfl fun _ _=> ih _ (he _)
   intro i _; exact invest_integrable l _ (he _)
end algebra

open Vessel
variable (z:ℕ×ℕ)
local notation "A!" => originBond P v β W A z
local notation "V!" => cargoShip P v W z
local notation "ξ!" => enter P v W A z
local notation "πZ" => ζbank P v z
local notation "F!" => ton ∘ (enter P v W A z)
def costing (A:ℝ)(l:List (Ball I))(x:grid P v z):ℂ:= -- notation A issue
  charge l * RoseGaussian.path ((l.map panelColor).map (originBond P v β W A z)) x
local notation "ℓP" => costing P v β W z -- check order A
variable [Fintype I]
lemma coloring (Z:φ z)(i:CTag I) : RoseGaussian.cost ((A!) i) Z=Complex.ofReal ((R z.1 A)^2 * (V!).siphon (χ₀ z) 1 0 P.par.K.top.clip i Z.val):= by
 -- Missing Fintype, add
 rw [RoseGaussian.cost,actual_tilt]
private lemma paying_piece (i:I) (k:CTag I → ℝ) : mPaint P v W A i z k =
    ∑ x:Blot, (pigment x * ( ((R z.1 A)^2 * k (i,x.1):ℝ) :ℂ)) • rollC (F!) (legs (i,x)) := by
 let V:= W i z.1; let Q:= O z; let M:= Zy z.1 A; let R':=R z.1 A; let S:=pickColor (Prod.mk i) k; let u(ρ:ℕ):= wrapCurrent V.u V.spin ρ Q; let B:= (EuclideanSpace.basisFun SU.group.ColorIndex ℝ).toBasis
 have hp:(M:ℂ)^3 • u 1 S=u M S:=by unfold u; rw [dgC,dgC, Nat.cast_one,one_pow,one_smul]
 have hv : mPaint P v W A i z k=(R':ℂ)^2 • u M S:=by rw [←hp,smul_smul]; unfold mPaint; change (↑(R'^2 * (M:ℝ)^3):ℂ) • _=_; norm_cast
 have hs(a):mug.coord a S=k (i,a):=by change (B.repr S a : ℝ)=_; rw [show B = (EuclideanSpace.basisFun SU.group.ColorIndex ℝ).toBasis from rfl, OrthonormalBasis.coe_toBasis_repr_apply]; rfl
 rw [hv, show S=∑ j:SU.group.ColorIndex,mug.coord j S • mug j from (mug.sum_repr S).symm,map_sum,Finset.smul_sum]; unfold Blot; rw [Fintype.sum_prod_type]; apply sum_congr rfl; intro x _
 rw [hs,map_smul]; unfold u; rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),tomato,smul_smul,Finset.smul_sum]
 conv_rhs => rw [Fintype.sum_prod_type]
 refine sum_congr rfl fun a v'=>?_ ; rw [Finset.smul_sum]; refine sum_congr rfl fun b v=>?_
 let X := sold M V.u V.spin (N:=Q) a b; let y:= colorEntry a b (mug x)
 rw [smul_smul]; change _ • X= _ • ((ton ((ξ!) (i,b,true)))* (ton ((ξ!) (i,a,false))*1))
 rw [mul_one]; apply congrArg (fun c:ℂ=> c • X); change ↑R'^2 * (k (i,x):ℂ) * y=y*↑(R'^2 * k (i,x)); push_cast; ring

-- Gaussian tap depiction at pose. Summing later.
def studying (A:ℝ)(Z:grid P v z)(K : Ball I): FC (Single (O z)):=
   (pigment K.2 * RoseGaussian.cost (originBond P v β W A z (panelColor K)) Z) • rollC (ton ∘ enter P v W A z) (legs K)

private lemma sprouts (Z:φ z)(l:List (Ball I)) :
   (l.map (studying P v β W z A Z)).prod= costing P v β W z A l Z • rollC (F!) (stream l):=by
 induction l with
 | nil=> rw [stream,List.flatMap_nil, costing,charge]; simp [rollC,RoseGaussian.path]
 | cons i l ih=>
    rw [List.map_cons,List.prod_cons,ih]; let a:=rollC (F!) (legs i); let b:=rollC (F!) (stream l); let x:=RoseGaussian.cost ((A!) (panelColor i)) Z
    rw [show stream (i::l)=legs i ++ stream l from rfl,show rollC (F!) (legs i ++ stream l)=a*b by simp only [rollC,List.map_append,List.prod_append]; rfl]
    change ((pigment i.2*x) • a) * ((_) • b)=_ • (a*b)
    rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul]; apply congrArg (fun x:ℂ=>x • (a*b)); unfold costing; simp only [List.map_cons,RoseGaussian.path_step]; change pigment i.2*x*(charge l*_)=_ -- scalar only
    unfold charge; rw [List.map_cons,List.prod_cons]; unfold x; ring

private abbrev ColorsAt (Z:grid P v z) : CTag I→ℝ:= Regis.Wake.drip ((V!).siphon (χ₀ z) 1 0 P.par.K.top.clip) Z.val
local notation "cZ" => ColorsAt P v β W z
private lemma contour (Z:φ z)(l:List I) : (l.map (fun i=> mPaint P v W A i z ((cZ) Z))).prod=deposits l (fun t => (t.map (studying P v β W z A Z)).prod):=by
 let f(i:I):=mPaint P v W A i z ((cZ) Z)
 let B:=studying P v β W z A Z; change (l.map f).prod=deposits l _
 rw [show f=fun i=>∑ b:Blot,B (i,b) from ?_,invest_mul l]
 funext i; unfold f B; rw [paying_piece]; refine sum_congr rfl fun b _=>?_; rw [studying,coloring]

lemma deposition (Z:φ z)(l:List I)(e:Kea.Pad P.par.K.j (O z)) : checkBy P v W l A z ((cZ) Z)=deposits l (fun t=> costing P v β W z A t Z * runes (meshRow P v W A z) (stream t)):=by
 rw [checkBy,contour]; let f : FC (Single (O z)) →+ ℂ:= (πZ).toAddMonoidHom
 change f (deposits l _) = _; rw [invest_sum]; apply invest_dep; intro o _; change (πZ) _= _; rw [sprouts,map_smul,season_f P v W z e]; rfl -- order tune

private lemma cash_pad (l:List (Ball I)) : Integrable (fun Z=>costing P v β W z A l Z) (μZ z):= (RoseGaussian.path_read _).const_mul _

noncomputable def roseMoment (L:List I)(f:sIndex I→sIndex I→ℂ)(V: CTag I→ CTag I →ℂ):ℂ:=
 deposits L (fun t=> charge t * RoseGaussian.exchange V t.length (t.map panelColor) * runes f (stream t))
lemma flower_price (L:List I)(h:Kea.Pad P.par.K.j (O z)) :
 seatT Y z.1 (pᵥ z) (cᵥ z) (cargoShip P v W z) (checkBy P v W L A z) (κFix β z.1)=roseMoment L (meshRow P v W A z) (fun i j=> RoseGaussian.cost ((A!) i) ((A!) j)):=by
 let F(t:List (Ball I))(Z:φ z) := costing P v β W z A t Z * runes (meshRow P v W A z) (stream t)
 change (∫ x:φ z, checkBy P v W L A z ((cZ) x)∂(μZ z))= _
 simp_rw [deposition (z:=z) P v β W _ L h]; rw [invest_integral L F (fun i _ => (cash_pad P v β W z i).mul_const _)]
 apply invest_dep; intro l hl; unfold F costing; rw [integral_mul_const,integral_const_mul,RoseGaussian.primitive (l.length) (A!) (l.map panelColor) (by simp)]
end Rose
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
