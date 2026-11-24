import YM.CF.Taxi.Boot
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Taxi
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
-- even-translation cells convolution. chosen *symmetrized* parity averaging over all signed.
section core
abbrev Marca:=Signed×Finset Axis
variable (o q:Site n)(T:Marca)
def boot(T: Marca):Site n:= T.1.act (∑ i∈T.2,(step i:Site n))
private lemma pin_d (s:Signed)(Y:Site n):pdist (s.act Y)=pdist Y:=by simpa [separation] using separation_signed Y 0 s
private lemma fallB (S:Finset Axis):pdist (∑ i∈S,(step i:Site n))≤S.card:=by
 induction S using Finset.induction_on with| empty=> simp only [sum_empty,card_empty]; simpa [pdist,Lattice.lift] -- tune
                                           | insert i S u ih=> rw [sum_insert u,card_insert_of_notMem u]; exact (pdist_triangle ..).trans ((add_le_add (pdist_step i) ih).trans_eq (add_comm ..))
lemma scale_b:pdist (boot (n:=n) T) ≤ 4:=by unfold boot; rw [pin_d]; exact (fallB _).trans T.2.card_le_univ -- tune
abbrev fs : ℝ := (Fintype.card Marca:ℝ)⁻¹
abbrev motto(o q:Site n):ℝ:= fs*∑ i:Marca, if q=o+boot i then (1:ℝ) else 0
set_option linter.constructorNameAsVariable false in
lemma mot_l :0 ≤ motto o q:= mul_nonneg (by unfold fs; positivity) (sum_nonneg (by intros x p; split<;> simp))
lemma mot_b : ∑ q:Site n,motto o q=1:=by
 unfold motto; rw [←mul_sum,sum_comm]; rw [sum_congr rfl (fun i _=> show (∑ x:Site n, if x=o+boot i then (1:ℝ) else 0)=1 from by simp),sum_const,card_univ,nsmul_eq_mul,mul_one]; apply inv_mul_cancel₀; exact_mod_cast Fintype.card_ne_zero -- tune
lemma motors (h:motto o q≠0):separation o q≤4:=by
 obtain ⟨i,-,u⟩:= exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul h); split at u; rename_i h; · rw [h,separation_comm,separation,add_sub_cancel_left]; exact scale_b _
 contradiction
lemma mot_g (s:Signed)(u: Site n): motto (affine s u o) (affine s u q)= motto o q:=by
 unfold motto; let L:Equiv.Perm Marca:=Equiv.prodCongr (Equiv.mulLeft s) (Equiv.refl _); rw [← Equiv.sum_comp L (fun i:Marca=> if _ = _ + (boot i:Site n) then (1:ℝ) else 0)]; apply congrArg; apply sum_congr rfl; intro i _; have he:affine s u (o+boot i)=affine s u o+boot (L i):=by change _= _+(s*i.1).act _; unfold affine boot; rw [s.act_add, Signed.act_mul,show (L i).2=i.2 from rfl]; abel
 rw [← he]; unfold affine; simp only [add_left_inj,s.act_injective.eq_iff]
lemma spent(o v: Site n) (f: Site n→ℝ)(h:∀ i:Site n,∀ j:Axis, f i=f (i+step j)) : f o=f v:=by
 let w:= route (lift o) (lift v) 1; have he:f o=f (Lattice.stop o w):=by
    suffices g:∀ l:Lattice.Walk,∀ o:Site n,f o=f (Lattice.stop o l) from g w o
    intro l; induction l with
    | nil=> exact fun _=>rfl
    | cons a l ih=>
       intro i; refine Eq.trans ?_ (ih (i+a.vec)); unfold Step.vec; split
       · rw [show f i= f ((i + - step a.dir)+step a.dir) from congrArg _ (by abel)]; exact (h _ _).symm -- tune
       exact h _ _
 have ht:=wrap_stop_cover (n:=n) (Lattice.lift o) w; rw [wrap_lift,show Lattice.stop (Lattice.lift o) w=Lattice.lift v from route_end ..,wrap_lift] at ht; rw [ht]; exact he
end core
-- period two any direction.E fixed v across Σ stencil. use toggle.
variable (U:Site (More n)→ℝ)(hB:∀ i:Site (More n),∀ x:Site n,U (i+(assembly n).embed x)=U i)
local notation "Q"=> More n
include hB
private lemma front_v (s:Signed)(i:Site Q)(a:Axis):U (i+s.act (step a)+s.act (step a))=U i:=by
 rw [show i+s.act (step a)+s.act (step a)= i+(assembly n).embed (s.act (step a)) from ?_]; apply hB
 rw [Ratio.signed]; have he:(assembly n).embed (step a)=step a+step a:=by rw [← wrap_step n, Ratio.embed_wrap,map_nsmul,wrap_step]; exact two_smul ..
 rw [he,s.act_add,add_assoc]
omit hB
private def flagX (a:Axis)(i:Finset Axis): Finset Axis:=if a∈i then i.erase a else insert a i
private lemma flag_l (a:Axis)(i:Finset Axis):flagX a (flagX a i)=i:=by unfold flagX; by_cases h:a∈i <;> simp [h]
private abbrev flagG (a:Axis):Equiv.Perm (Finset Axis):= ⟨flagX a,flagX a,flag_l a,flag_l a⟩
abbrev spanK (s:Signed)(U: Site n→ℝ)(x:Site n):ℝ:=∑ i:Finset Axis,U (x - boot (s,i))
include hB
lemma freeR (s:Signed)(a:Axis)(x:Site Q): spanK s U (x+s.act (step a))=spanK s U x:=by
 unfold spanK; rw [←Equiv.sum_comp (flagG a)]; apply sum_congr rfl; intro i p; change U (x+s.act (step a)-s.act (∑ j∈flagX a i,step j))=U (x-s.act (∑ j∈i,step j))
 by_cases g:a∈i; swap; · rw [flagX,if_neg g,sum_insert g,s.act_add]; apply congrArg; abel
 rw [flagX,if_pos g]; let V:=s.act (step a:Site (More n)); let K:=s.act (∑ j∈i.erase a,(step j:Site (More n))); have hv:s.act (∑ j∈i,(step j:Site (More n)))= V+K:=by rw [← Finset.add_sum_erase _ (step (S:=Per (More n))) g,s.act_add] -- tune lemma
 rw [hv,show x+s.act (step a)-K=x-(V+K)+V+V from (by unfold V; abel)]; exact front_v U hB s _ a
lemma penM (s:Signed)(o q:Site Q): spanK s U o=spanK s U q:=by
 apply spent; intro i j; obtain ⟨j,rfl⟩:=s.perm.surjective j; let d:=posDir j; have ht: s.act (step j:Site Q) = (d.rotate s).vec:= (show _ from (by rw [Step.vec_rotate]; rfl)); have he(x): spanK s U (x+(d.rotate s).vec)=spanK s U x:=ht ▸ freeR U hB s j x -- tune ▸
 cases g:s.flip j; · specialize he i; simp [Step.rotate,Step.vec,g,d,posDir] at he; exact he.symm
 apply Eq.trans (_ : spanK s U i = spanK s U ((i+step (s.perm j))+(d.rotate s).vec)) (he (i+step (s.perm j))); apply congrArg; simp [Step.rotate,Step.vec,g,d,posDir] -- tune
lemma blareR (o:Site Q): ∑ x:Site Q,motto x o * U x= fs * ∑ s:Signed,spanK s U 0:=by
 have he (x:Site Q) (i:Marca): o=x+boot i↔ x=o-boot i:= ⟨fun h=> by rw [h]; abel, fun h=> by rw [h]; abel⟩
 unfold motto; rw [show (∑ x:Site Q,_)=fs * ∑ i:Marca,∑ x:Site Q,(if o=x+boot i then (1:ℝ) else 0)*U x from ?_, Fintype.sum_prod_type]; swap; · rw [sum_comm,mul_sum]; simp_rw [mul_assoc, Finset.sum_mul]
 apply congrArg; apply sum_congr rfl; intro i _; rw [← penM U hB i o]; unfold spanK; apply sum_congr rfl; intro j w; simp [he]
end YM.CF.Taxi
