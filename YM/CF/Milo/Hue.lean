import YM.CF.Milo.Table
import YM.CF.Milo.Foil
import YM.CF.Milo.Sucre
import YM.CF.Milo.Leg
import YM.CF.Sour.Rate
import YM.CF.Sour.Millet
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
namespace Glyph
variable {δ a b u e W:ℝ}{μ:Toll (Single n)}{S:Support (More n)}
variable (F:Raw (Openc (More n) δ) (Single n)){q:ℕ}{K:Scree.Loom n}(p:Roof n a δ q K)(g:0<δ)(t: Suite (badge _) (bail n δ) (bail n δ) S μ F)
variable {H:Op (Single n)→FC (Dwell n)}{Z':Single n→ Single n→ FC (Dwell n)}{h:ℝ}(f: Glyph H Z' h)
variable (T:Scree.Hub n)(z:T.val.1∈ S)(x:S∈αW P.B (Bake.lagE T))
local notation "B"=> P.B
local notation "Y'"=> Bake.lagE T
local notation "Xv"=> Glyph.cure H p g F
variable (v: q+10≤ P.B)(r:P.threshold ≤ a) (A:Ids n)(V: Pane n)
open Ione Bake Nor Larch
local notation "Hz"=>Scree.Hub n
variable (p0:HopeT δ b e P.order)(s:P.threshold ≤ e)(hQ:cipherK q ≤5*P.B)(hB:3≤P.B)(hx:1 ≤ h) (Q:Support (More n)→ Toll (Single n))(F':Support (More n)→ Raw (Openc (More n) δ) (Single n))(qF:∀ S,Suite (badge _) (bail n δ) (bail n δ) S (Q S) (F' S))
open Palot
def écu (T:Hz):ℝ:=∑ U∈ panel P T,pay_η (P:=P) (h:=h) Q U
def slice(P:BudgetPoint)(U: VX)(j:SO):Finset (Hz):= (Ione.web0 U).filter fun i=> j ∈ panel P i
variable (YV:Aura n)
lemma bro_K(j:SO) (p:j∈αW P.B YV): let s:= slice P YV j
 (∀ R∈ s,R.val.1∈j) ∧ s.card=j.card ∧ j.card≠0:=by
 intro u; have ht(T:Hz)(v:T∈ web0 YV):j∈ panel P T↔ T.val.1∈j:=by unfold panel; rw [(mem_filter.mp v).2,mem_filter,and_iff_right p]
 have hx:j ⊆ YV.val:= (mem_filter.mp p).2 ▸ halo_subset _ _; let f(i:↥j):Hz:=⟨(i,YV.val),hx i.property⟩; have hv:Injective f:=fun i j h=>Subtype.ext (congrArg (fun p:Hz=> p.val.1) h); have hh: univ.image f=u:=by
    ext T; simp only [mem_image,mem_univ,true_and]; constructor
    · rintro ⟨i,rfl⟩; have he:f i∈ web0 YV:=mem_filter.mpr ⟨mem_univ _,Subtype.ext rfl⟩; exact mem_filter.mpr ⟨he,(ht _ he).mpr i.property⟩
    intro k; obtain ⟨y,q⟩:=mem_filter.mp k; exact ⟨⟨T.val.1,(ht _ y).mp q⟩,Subtype.ext (Prod.ext rfl (congrArg Subtype.val (mem_filter.mp y).2.symm))⟩
 refine ⟨fun R v=>(ht _ (mem_filter.mp v).1).mp (mem_filter.mp v).2,by rw [←hh,card_image_of_injective _ hv,card_univ,Fintype.card_coe],?_⟩ -- tune
 apply Nat.ne_of_gt; rw [card_pos]; obtain ⟨x,t⟩:=YV.property; rw [(mem_filter.mp p).2] at t; obtain ⟨i,t,h⟩:=halo_spec.mp t; exact ⟨_,t⟩
variable(Vx: Skye.Orbit n)
include qF p0 s hQ hB hx p f r v g
local notation "W_'"=> vote
lemma puff : (∑ R∈ Ione.web0 YV,(doveK p g F' P H R) Vx.1).val= Sault.rind (coll_T P YV ∅ (actsF H F' p g P.B YV) Vx):=by
 let S:=Ione.web0 YV; let U:=αW B YV; let A(j:SO):= coll_T P YV ∅ (Glyph.cure H p g (F' j)) Vx
 have he:coll_T P YV ∅ (actsF H F' p g P.B YV) Vx=∑ j∈U,A j:=by
    unfold coll_T; split_ifs with v
    · rw [actsF,Finset.sum_apply]; exact sum_congr rfl fun j _=> (if_pos v).symm
    simp [A,coll_T,v]
 let F(T:Hz)(j:SO):Γ:= ((j.card:ℝ)⁻¹ •(W_' (F' j) p g P H T Vx.1)).val -- accidental smul type coer.
 rw [show (∑ R∈_,_)=∑ R∈S,(doveK p g F' P H R) Vx.1 from rfl]; change (Dough (Dwell n)).val _ = _
 rw [he,map_sum,Sault.rind,map_sum]; change (∑ R∈ S,_) = _
 have hp(T:Hz)(q0:T∈S): (doveK p g F' P H T Vx.1).val=∑ j∈U, if j∈panel P T then F T j else 0:=by
    rw [←sum_filter]; have hx:= (mem_filter.mp q0).2; have hh: U.filter (fun j=> j∈panel P T)=panel P T:=by ext j; rw [Finset.mem_filter]; exact and_iff_right_of_imp fun s=> (show j∈αW P.B YV from hx ▸ (mem_filter.mp s).1) -- tune
    rw [hh]; unfold doveK; rw [Finset.sum_apply]; exact map_sum (Subalgebra.val _) ..
 change ∑ R∈S,(doveK _ _ _ _ _ R Vx.1).val = ∑ i∈U,Sault.rind (A i)
 rw [sum_congr rfl hp,sum_comm]; refine sum_congr rfl fun j u=>?_ ; rw [←sum_filter]
 have hg:=bro_K (P:=P) YV j u; let d:ℝ:=j.card; let K(T:Hz):= d⁻¹ • Sault.rind (A j)
 have hv(T:Hz)(p':T∈ slice P YV j): F T j= d⁻¹ • Sault.rind (A j):=by
    obtain ⟨r',v'⟩:=mem_filter.mp p'; have hlag:lagE T=YV:= (mem_filter.mp r').2; have hw:= express (F' j) p g (qF j) f T (hg.1 T p') (hlag.symm ▸ u) v r p0 s hQ hB hx -- hx shadow
    change _ • (vote (F' j) p g P H T Vx.1).val= _; rw [hw.1 Vx,hlag]
 change ∑ i∈slice P YV j,F i j=_; rw [sum_congr rfl hv,sum_const,hg.2.1,←Nat.cast_smul_eq_nsmul ℝ]; exact smul_inv_smul₀ (show d≠0 by unfold d; exact_mod_cast hg.2.2) _
omit qF p0 s hQ hB hx p f r v g
include qF
lemma tally_i(o:SA): (∑ i:Hz, if i.val.1=o then P.mass i.val.2 (écu (P:=P) (h:=h) Q i) else 0) ≤ ∑ j∈hit0 o,(P.order+1:ℝ)*h^2* worth P Q j:=by
 let V:=univ.filter fun i:Hz=>i.val.1=o; let F(i:Hz)(j:SO):=P.mass i.val.2 (pay_η (P:=P) (h:=h) Q j)
 have hp(i:Hz): P.mass i.val.2 (écu (P:=P) (h:=h) Q i) = ∑ j∈panel P i,F i j:=by unfold écu BudgetPoint.mass; rw [mul_sum]; rfl
 rw [←sum_filter]; simp_rw [hp]; rw [sum_sigma']; let B':= V.sigma fun i=>panel P i; let H:=B'.image Sigma.snd; have ht(i:Hz)(u:i∈ V)(x:SO)(p:x∈panel P i):o∈ x∧i.val.2=halo B x:=⟨(mem_filter.mp u).2 ▸ (mem_filter.mp p).2,(mem_filter.mp ((mem_filter.mp p).1)).2⟩
 refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg (show H⊆ hit0 o from ?_) (fun i _ _=>mul_nonneg (by positivity) (shelf_s P Q (fun S=> (qF S).toTicket) i)))
 · unfold H; rw [sum_image]; refine sum_le_sum fun i t=> ?_; obtain ⟨v,f⟩:=mem_sigma.mp t; obtain ⟨a,x⟩:=ht _ v _ f; unfold F BudgetPoint.mass pay_η; rw [x]; let C':=Glyph.vest P h (Q i.2); let d0:ℝ:= i.2.card; have hd:1 ≤ d0:=by unfold d0; exact_mod_cast (show 1 ≤ i.2.card from card_pos.mpr (show i.2.Nonempty from ⟨_,a⟩));
   refine (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left ?_ (inv_le_one_of_one_le₀ hd)) (Real.exp_pos _).le).trans_eq ?_
   · exact mul_nonneg (health_f ..) (mul_nonneg (mul_nonneg (by positivity) (sum_nonneg fun i _=> sum_nonneg fun j _=> (qF _).nonn i j)) (by positivity))
   · unfold vest Sour.worth Push.AbsoluteSums.Trees.currency; ring
   rintro ⟨x,y⟩ u ⟨w,z⟩ v e; change y=z at e; obtain rfl:= e; obtain ⟨k,f⟩:= mem_sigma.mp u; obtain ⟨g,p⟩:= mem_sigma.mp v; have hh:x=w:=Subtype.ext (Prod.ext ((mem_filter.mp k).2.trans (mem_filter.mp g).2.symm) ((ht x k y f).2.trans (ht w g y p).2.symm)); rw [hh]
 intro i t; obtain ⟨j,v,rfl⟩:= mem_image.mp t; obtain ⟨k,f⟩:=mem_sigma.mp v; exact mem_filter.mpr ⟨mem_univ _,(ht _ k _ f).1⟩
end Glyph
end YM.CF.Sour
