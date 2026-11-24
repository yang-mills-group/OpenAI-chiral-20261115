import YM.CF.Yaw.Own
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Yaw
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Eire Jet Scroll Push.AbsoluteSums.Trees
variable {ι:Type}
local notation "bay"=> Stilo.bay
open PetalP
variable {N P B:Side}(S:StepData (Domain N B) (Domain P B)){r D:ℕ}
open Rush Scroll Paige Vault Phase Acorn Spire
variable {A:Side}{j k:ℕ}{o:Odd A.val}{Y:Pricing j A o (Thread j)}{e:ℝ}{q:Grasp Y B e}{I:Aim (mid P B)}{M:Male}{α K K' t a d C H:ℝ}
variable (V: ∀ A:Support (Domain P B),Lend P B e A)(X:Tints P B e)
local notation "V'"=> Domain P B
local notation "L'"=> Oboe (Single (mid P B))
variable (i:Hos S r)(κ:ℕ)(t':Support (Domain P B)× Support (Domain P B))
local notation "uT"=> danceL S i.val r
local notation "χH"=> Eire.frameP S (i,t')
local notation "CE"=> (Push.AbsoluteSums.Trees.currency)
variable {c Z α α':ℝ}{B0 s:ℕ}
lemma pace_m : stem S i⊆ hatY S (danceL S i.val r):=by
 intro j v; let x:= S.ratio.embed j; have hp:S.ratio.parent x=j := Ratio.embed_parent ..; exact mem_image.mpr ⟨x, dance_cover S _ (hp.symm ▸ v),hp⟩
lemma lit_price (h:Grove (terr _) t'.1)(v:Grove (terr _) t'.2)(p:uT⊆ t'.1)(g:uT⊆t'.2)(b:0<B0)(f:0≤c)(e:κ≤ s*B0)(y: c *2*Yaw.χ s ≤ B0*Z)(z:c *2*Yaw.χ s ≤ B0*α')(hq:0≤Z)(ht:0≤α'):
 CE B0 c (Lattice.halo κ χH) ≤ (Real.exp (c *Yaw.χ s)*Branch.rent Z uT)*(Real.exp (c *Yaw.χ s)*Branch.rent α' uT)*(Acorn.cost Z uT t'.1* Acorn.cost α' uT t'.2):=by
 have he:χH= hatY S t'.1∪ hatY S t'.2:=by dsimp only [Eire.frameP]; rw [union_eq_right.mpr p]; unfold hatY; rw [image_union]; apply union_eq_right.mpr; exact (pace_m S i).trans ((image_subset_image p).trans subset_union_left)
 let A:=Lattice.halo κ (hatY S t'.1); let B:= Lattice.halo κ (hatY S t'.2); have hx:Lattice.halo κ χH=A∪B:=by rw [he]; ext; simp only [halo_spec,mem_union]; unfold A B; simp only [halo_spec,←exists_or]; grind
 have hv{X:Support V'}(h:uT ⊆ X)(v:ℝ): Branch.rent v X=Branch.rent v uT*Acorn.cost v uT X:=by unfold Acorn.cost Branch.rent; rw [← Real.exp_add, ←mul_add,card_sdiff_of_subset h,Nat.cast_sub (card_le_card h), add_sub_cancel]
 rw [hx]; have hg: CE B0 c (A∪B)≤ CE B0 c A*CE B0 c B:=by
    obtain ⟨x,v⟩:=stem_p S i; have ha:= (pace_m S i) v; unfold Push.AbsoluteSums.Trees.currency; rw [←Real.exp_add, ←mul_add]; exact Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast Corona.meets_sum (show x∈ A from halo_subset _ _ (image_subset_image p ha)) (show x∈B from halo_subset _ _ (image_subset_image g ha)) B0) f)
 refine hg.trans ((mul_le_mul (aidV S.ratio h e b f y hq) (aidV S.ratio v e b f z ht) (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (rent_pos _ _).le)).trans ?_); rw [hv p,hv g]; exact le_of_eq (by ring)
abbrev luxH (t:Support V'→ℝ)(i:Hos S r)(x:Sweep (mid P B))(a:ℕ)(l:Support V'×Support V'):= root_g a V (danceL S i.val r) x l t
variable (g:Sweep (mid P B))(G: Ids (mid P B))(p:Hive.chip (danceL S i.val r) G=g) (q0:ShiftD k K' K e (danceL S i.val r) G g)(w:Vista q M I V k K ((Fintype.card Play:ℝ)*t) d C)
variable {D W:ℝ}
local notation "γM"=> (Real.exp (c *Yaw.χ s)*Branch.rent α uT)
include q0 G w
lemma talc(T':Support V'→ℝ)(h:∀ Y,T' Y ≠0 → uT ⊆ Y∧ Grove (terr V') Y)(u:(∑ Y:Support V',Acorn.cost α uT Y*T' Y)≤D)(ht:0≤T') (b:0<B0)(f:0≤c)(v:0≤α)(f':0≤C)(eK:κ≤ s*B0)(y:c *2*Yaw.χ s ≤ B0*α)(z:c *2*Yaw.χ s ≤ B0*C)(v':0≤t): (∑ Y:Support V' ×Support V', CE B0 c (Lattice.halo κ (Eire.frameP S (i,Y))) *loadH (luxH S V T' i g k Y) t) ≤ γM*(Real.exp (c *(Yaw.χ s:ℝ))*Branch.rent C uT)*(((k+1:ℝ)^2*D)* Real.exp (d*((danceL S i.val r).card:ℝ)*((Fintype.card Play:ℝ)*t)^2)):=by
 obtain ⟨p',k'⟩:=swing_a uT V g G q0 (dance_g S i) w; let H(Y):= luxH S V T' i g k Y; have hv(Y):0≤ (H Y).led:= duty_p V uT G g p' Y (ht _); have hl(Y):0≤loadH (H Y) t:= sum_nonneg (fun j _=>mul_nonneg (hv Y j) (pow_nonneg v' _))
 let U(Y:Support V'× Support V'):=loadH (H Y) t; refine le_trans ?_ (mul_le_mul_of_nonneg_left (hire_l V uT G g p' α t C 0 D _ v' ht u k') (mul_nonneg (mul_nonneg (Real.exp_pos _).le (rent_pos _ _).le) (mul_nonneg (Real.exp_pos _).le (rent_pos _ _).le))); rw [Finset.mul_sum]; apply sum_le_sum; intro Y _; change _* U Y≤ _* (_* U Y); rw [←mul_assoc]; by_cases x: U Y=0; · simp [x]
 obtain ⟨j,p',k⟩:= exists_ne_zero_of_sum_ne_zero x; have hx:= host_l V uT G g (swing_a uT V g G q0 (dance_g S i) w).1 Y h (W:=T') j (left_ne_zero_of_mul k); exact mul_le_mul_of_nonneg_right (lit_price S i κ Y hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 b f eK y z v f') (hl Y)
end YM.CF.Yaw
