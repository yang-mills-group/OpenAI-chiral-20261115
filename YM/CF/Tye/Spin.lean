import YM.CF.Tye.Muse
import YM.CF.Lich.Spear
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Tye
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Corne Lich Lich.Muster Rink Jet Vol
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}
variable {x e m:ℝ}(A:Muster G S x e T)(M:Monk SU.group S)(s:Signed)(b:Site (Domain N B))(g:Site (Domain N B)→ SU.group.El)
open AnalyticBridge.GaussianFieldAlignment Tensor Orthogonal PhysicalNext.OrderedAffine2B.SymRows Channels Locations
variable {d:ℕ}
local notation "Y"=> clue S s b M
local notation "V"=> shiftZ g M
local notation "F"=> cedar M
variable (h:K.Funds S T)(hp:FreeResolvent.Gap (baseX T x M.key M.park M.k M.V) m)(hv:120 ≤ radiusB x)(hz:0 < m)(hA: Reef.Rare T.up)(hB:Reef.Rare T.down)(ht: LocalRatio A.vita)(hi:0 < A.rota)(hm:4*A.rota < A.vita.radius)(hb:0 < A.beta)
local notation "d"=> Domain N B
local notation "d'"=> Domain P B
local notation "L"=> Stores.till x
open Font Nacre
def stock (i:Site (More N)): Op (Single N) := Matrix.diagonal (fun x=> if place_x x=i then (1:ℂ) else 0)
def halfY {n:Type*}[Fintype n](A' : Op n): Op n:=(1/2:ℂ) • A'
def doubleK (D:Op (Single N))(i:Site (More N)): Op (Single N):= halfY (stock i*D+D*stock i)
lemma stockX (i:Site (More N))(b:Bool): star (stock i)=stock i ∧ windX b (stock i)=stock i:=by
 constructor; ext a c; change star (stock i c a)= stock i a c; by_cases h:a=c; subst a; simp [stock, apply_ite star]; simp [stock,h,(Ne.symm h)]; cases b; rfl; ext a c; change star (stock i a c)= stock i a c; by_cases h:a=c; subst a; simp [stock,apply_ite star]; simp [stock,h]
lemma cupZ {N:Side}(ι: Site (More N))(Q': Op (Single N)) : (stock ι)*Q'=Matrix.of fun i j=> if place_x i=ι then Q' i j else 0:=by ext i j; simp [stock,Matrix.diagonal_mul,ite_mul]
lemma capZ {N:Side}(ι:Site (More N))(Q': Op (Single N)): Q'*stock ι=Matrix.of fun i j=> if place_x j=ι then Q' i j else 0:=by ext i j; simp [stock,Matrix.mul_diagonal,mul_ite]
lemma stamp_s {N:Side} (Q:Op (Single N)): ∑ i,doubleK Q i=Q:=by
 unfold doubleK halfY; simp_rw [←smul_sum,capZ,cupZ]; ext i j; change (1/2:ℂ)*(∑ v,((Matrix.of _) +(Matrix.of _):Op (Single N))) i j= _; simp [Matrix.sum_apply,sum_add_distrib]; ring -- tune change holes modulo
abbrev inkPH(A:Shape)(b:Bool)(Q:UNI SpinIdx)(s:Op (Single N)):= sings b (prepU A Q (xtra b) N) s
lemma birth_l(i j:Single N)(a: Shape)(U:UNI SpinIdx)(b:Bool)(p:(prepU a U (xtra b) N).val i j ≠0): a.anon _ (place_x i)=place_x j := by
 rcases i with ⟨⟨x,i⟩,u⟩; rcases j with ⟨⟨y,j⟩,z⟩; change jump (Tofu a N) (fun i=>(milU a U (xtra b) i).val) (x,(i,u)) (y,(j,z))≠0 at p; rw [jump_apply] at p; have he : a.mills N x=y:=by split at p; assumption; contradiction
 rw [←he]; exact (a.nodex _).symm
lemma birth_g(i j:Single N)(g:Seat N→SU.E)(p:(tradew N g).val i j ≠0):place_x i=place_x j:=by
 by_contra h; exact p ((Tulip.bail N 0).keeps g i j h) -- tune
lemma proM (W: Site (More N)→ Site (More N)) (h:Injective W)(b:Bool)(U:UNI (Single N))(p:∀ i j,U.val i j≠0→ W (place_x i)=place_x j) (i:Site (More N)):sings b U (stock (W i))= stock i:=by
 rw [singT,(stockX _ b).2,twist_formula,show U.val*stock (W i)=stock i*U.val from ?_,mul_assoc,U.property.2,mul_one]; rw [capZ,cupZ]; ext j k; by_cases z:U.val j k=0; simp [z]; simp only [Matrix.of_apply]; rw [←p _ _ z]; simp [h.eq_iff] -- rw depend
lemma tourZ {n:Type*}[LinearOrder n][Fintype n](b r:Bool)(U:UNI n)(W D E:Op n)(h:sings b U D=E)(p:star E=E): Thera.jazz r (sings b U (halfY (D*W+W*D)))=halfY (E*Thera.jazz r (sings b U W)+Thera.jazz r (sings b U W)*E):=by
 have he(Q:Op n): sings b U (halfY Q)=halfY (sings b U Q):=by
    unfold halfY; rw [singT,singT, win_c,twist_scalar]; cases b; rfl; simp only [cSignX,ite_true,star_div₀,star_one,star_ofNat] -- tune
 let Q:=sings b U W; have ht: sings b U (halfY (D*W+W*D))=halfY (E*Q+Q*E):=by rw [he,singT,win_a,map_add,win_m,win_m,map_mul,map_mul, show twist U (windX b D)=_ from h]; rfl
 rw [ht]; cases r; rfl; change - star (halfY (E*Q+Q*E))=halfY (E * -star Q + -star Q * E); unfold halfY; rw [star_smul,star_add,star_mul,star_mul,p, star_div₀,star_one,star_ofNat]; simp only [mul_neg,neg_mul,←neg_add,smul_neg,add_comm]
lemma voteZ(b r:Bool)(U:UNI (Single N))(P':Op (Single N))(i j:Site (More N))(hp:sings b U (stock i)=stock j): Thera.jazz r (sings b U (doubleK P' i))=doubleK (Thera.jazz r (sings b U P')) j:= tourZ b r U P' _ _ hp (stockX _ b).1
variable {κ w:ℝ}{r n:ℕ}{K' E τ:ℝ}
local notation "Ω"=> mid N B
variable (U' : Sweep (mid N B))(i:Site (Domain N B))(C:UNI SpinIdx)(S':Rent0 G e) (W':Op (Single (mid N B))) (p:JetS U'.s U'.charge (detX U'.s) C)
local notation "X"=>castX U'
local notation "D"=> yank U'.charge (castX U') C
lemma piece_y: doubleK (D W') i=D (doubleK W' ((castX U').anon _ i)):= (voteZ _ _ _ _ _ _ (proM _ (Shape.anon_b _).1 U'.charge _ (fun j k h=> birth_l _ _ _ _ U'.charge h) _)).symm
lemma piece_g (g:Seat (mid N B)→ SU.E):ActZ g (doubleK W' i)=doubleK (ActZ g W') i:= by exact (voteZ false false _ _ _ _ (proM id (Function.injective_id) false _ (fun i' j p=>birth_g i' j g p) i)) -- Seat namespace tuning
variable {Ξ_:nomA N P B→Op (Single (mid N B))}(hI: Ind G A.Fame κ w K' n Ξ_)
local notation "θ"=> A.Fame
include p hI
lemma fame_s (v: Support (Domain P B)) : A.Fame (toRoar G U'⁻¹ v) (male e G U' S')=D (A.Fame v S'):=by rw [hI.motion]; exact Cour.turn_r _ _ _ C _ (spinZ U'.charge U'.s) p
lemma yes(D': Finset (Support (Domain P B)))(f:Support (Domain P B)→ Op (Single (mid N B))): ∑ i∈D',D (f i)= D (∑ i∈D',f i):=by
 unfold Cour.yank; simp_rw [Cour.turnsH,singT]; rw [win_sum,map_sum]; unfold Thera.jazz; split; rw [star_sum,sum_neg_distrib]; rfl
lemma med_s : Corne.led G x θ (male e G U' S')=D (Corne.led G x θ S'):=by
 unfold led; rw [← yes A U' C p hI]; symm; refine sum_equiv (weaveS G U'⁻¹) ?_ (fun i _=>(fame_s A U' C S' p hI i).symm)
 intro i; simp only [portA,mem_filter,mem_univ,true_and, rumR]
omit p
variable (g':Site (Domain P B) → SU.E)
lemma med_g : Corne.led G x θ ((dressL G e).dress g' S')=ActZ (scaleG G g') (Corne.led G x θ S'):=by
 unfold led ActZ; obtain ⟨v,H,-⟩:=hI.port; rw [map_sum]; exact sum_congr rfl fun i _=>(H i).gauge g' S'
end YM.CF.Tye
