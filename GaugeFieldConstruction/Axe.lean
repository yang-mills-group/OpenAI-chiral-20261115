import YM.CF.Sour.Cherry
import YM.CF.Levier.Ambo
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 30000
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
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial
-- sweep weight.TIO. openc slice.S.inverse. erosion
open Levier Thera Urn Nacre Salt

namespace SliceRoof
variable {N:Side}(U:Pane N) {e d a b t:ℝ}
local notation "JP" => (Single N)
abbrev Lantern (N:Side)(d:ℝ):Type:= ↥(Openc (More N) d)
lemma lantern (h:Guard U d)(p:0<d): Tulip.profile U∈Openc (More N) d:=by exact ⟨U,h,by simpa only [sub_self,norm_zero]⟩
abbrev light (d:ℝ) (U:Pane N)(p:0<d)(h:Guard U d) : Lantern N d:=⟨Tulip.profile U,lantern U h p⟩
def groupShape (F: Elm N Unit d a b):Prop:= ∀ s:Sweep N, leafJ s true F F
-- selfadjointity on physical guards only, keep actual Openc laws ON witnesses used later
abbrev ivory (F:Elm N Unit d a b)(p:0<d)(U:Pane N)(h:Guard U d) (X:Support (More N)):= F.F X () (light d U p h)
def pure_Rim (F: Elm N Unit d a b): Prop:= ∀ S x (U:Pane N),Guard U d→ (x:↥(Openc (More N) d)).val=Tulip.profile U→ star (F.F S () x)= F.F S () x
def rimStar (F:Elm N Unit d a b) : Elm N Unit d a b where
 F X i := glaze d (F.F X i)
 W X := Function.swap (F.W X)
 coat X := ⟨fun i=> bits d (F.W X) X (F.F X i) (F.coat X|>.1 i),fun _=> continuous_of_const (fun _ _=>by congr)⟩
 bank:= F.bank.flip

def rimMean (F:Elm N Unit d a b) : Elm N Unit d a b:=by
 let Z:=F.plus (rimStar F); let c:ℝ:=1/2
 refine ⟨fun X i z=> (c:ℂ) • Z.F X i z,fun X i j=> ‖(c:ℂ)‖ * Z.W X i j,fun X=>⟨fun i=> (Z.coat X|>.1 i).accel (c:ℂ),fun i=> continuous_of_const (fun _ _=>by congr)⟩,?_⟩
 have he:= Z.bank.funds (norm_nonneg (c:ℂ)); exact he.book (by unfold c; rw [Complex.norm_real, Real.norm_of_nonneg (by norm_num: (0:ℝ)≤ 1/2)]; linarith)
private lemma flip_light (U:Pane N)(x: Openc (More N) d) (h:x.val=Tulip.profile U): Sour.flit d x=x:=by apply Subtype.ext; change ice x.val=x.val; rw [h,ice_pr]
private lemma mean_r (F:Elm N Unit d a b)(x:Openc (More N) d)(U:Pane N)(h:x.val=Tulip.profile U)(S:Support (More N)):
  (rimMean F).F S () x=(1/2:ℝ) • (F.F S () x+star (F.F S () x)):=by let z:= F.F S () x; let j:ℝ:=1/2; change ((j:ℝ):ℂ) • (z+star (F.F S () (Sour.flit d x)))= _; rw [flip_light _ x h,Complex.coe_smul]
lemma rimMean_is (F:Elm N Unit d a b) :pure_Rim (rimMean F):=fun S x U _ e=>by rw [mean_r F x U e,star_smul,star_add,star_star,star_trivial,add_comm]
lemma rimMean_near (F:Elm N Unit d a b)(p:BeatL N)(u: NearL F (fun _=>p))(k:∀ U:Pane N,Guard U d→ star (p (Tulip.profile U))=p (Tulip.profile U)): NearL (rimMean F) (fun _=>p):=by
 rintro ⟨⟩ x V t e; simp_rw [fun s=> mean_r F x V e s]; rw [← smul_sum,sum_add_distrib,←star_sum]; let z:=p x.val
 have hh : z=∑ S,F.F S () x:=u () x V t e; have hw:star z=z:=by unfold z; rw [e]; exact k _ t
 change z=_; rw [←hh,hw, ←two_smul ℝ z,smul_smul]; norm_num
lemma realR_bridge (s:Sweep N)(P Q:Op JP): realR s true (P+Q)=realR s true P+realR s true Q:=by
 cases hp:det_S s <;> simp only [realR,ite_true,bolt,hitL,Thera.jazz];
 all_goals change (if det_S s then _ else _) = _; simp_all [det_S] <;> abel
lemma realR_sky (s:Sweep N)(P:Op JP): star (realR s true P)=realR s true (star P):=by simp only [realR,ite_true,bolt,hitL,Thera.jazz,singT,win_s,map_star]; split_ifs <;>simp only [star_neg]
lemma rimMean_group (F:Elm N Unit d a b)(q:groupShape F) :groupShape (rimMean F):=by
 rintro s ⟨⟩ S V x v; rw [mean_r _ x _ v, mean_r F (Sour.fog s d x) (flashA s V) (Sour.real_box s _ V _ v),q s () S V x v,← Complex.coe_smul,←Complex.coe_smul,real_t s true,realR_bridge s,realR_sky] -- fix order Real -> both sides
private lemma spinh (d e:ℝ)(p: BeatL N)(u:Solo e b p d):∃ X:Elm N Unit d e b,NearL X (fun _=>p):=by
 obtain ⟨F,C,V,E,h⟩:=u; let D:Elm N Unit d e b:=⟨fun X _=>F X,C,fun X=>⟨fun _=>V X,fun _=> continuous_const⟩,E⟩; exact ⟨D,fun j y _ _ _=> h y⟩
open Laic Moire
lemma group_stamp (d e:ℝ)(p: BeatL N)(u:Solo e b p d)(h:∀ (s:Sweep N) (V:Pane N), Guard V d → p (Tulip.profile (flashA s V))=realR s true (p (Tulip.profile V))):∃ X: Elm N Unit d e (Tenant.quota^2*b), NearL X (fun _=> p) ∧ groupShape X:=by obtain ⟨F,e⟩:= spinh d e p u; exact ⟨loopF F true,port_k _ _ _ e (fun s _ V hp=> h s V hp),fun s=>fla s F true⟩ -- syntax ..
-- choose radius d BEFORE pearl, prices h after. Keep exactly same P argument even after using noncanonical phase.
abbrev halfBand (N:Side):Op (Single N):=(1/2:ℝ) • 1
abbrev hemi_L (N:Side)(j:ℕ)(M: Male)(x:Chin N):Op (Single N):=funde j M N x-halfBand N -- replace spelling
lemma hemi_q (j:ℕ)(p:1 ≤ j): ∃ D> (0:ℝ), ∃ a>(0:ℝ), ∃ C> (0:ℝ),∃ n0:ℕ,∀ N:Side,n0 ≤ N.val →∀ (d:ℝ),0<d → d ≤ D→∀ M: Male,
   IsStarProjection (spar j M (1:Pane N)) ∧ (∀ V:Pane N, Guard V d→ IsStarProjection (spar j M V)) ∧
    ∃ F:Elm N Unit d a C, NearL F (fun _=> hemi_L N j M)∧ groupShape F∧ pure_Rim F :=by
 obtain ⟨a,B,e,h,hB,E,v,r⟩:=funde_s j p
 obtain ⟨k,g,u,V⟩:= Tulip.funde_q j p
 obtain ⟨d,hq,t,W⟩:= Scroll.radiance j p -- extra args?
 let f:=1/2*(Real.exp a); let C:=(Tenant.quota^2)*(B+f); refine ⟨min e (min k d),lt_min E (lt_min g hq),a,h,C,?_,max v (max u t),fun N q d₀ δ y M=>?_⟩
 · unfold C; have he:0<Tenant.quota:=by have hp:= Tenant.quota_bound; linarith -- tune
   unfold f; positivity
 have he(x:Pane N)(e:Guard x d₀) : IsStarProjection (spar j M x) := V M N ((le_max_left u t|>.trans (le_max_right ..)).trans q) x (e.shrink ((y.trans (min_le_right ..)).trans (min_le_left ..)))
 refine ⟨he 1 (guard0 δ.le),he,?_⟩; let Y:= hemi_L N j M
 have hp: Solo a B (funde j M N) d₀:= axis_down a B (r M N ((le_max_left ..).trans q)) _ δ (y.trans (min_le_left ..))
 have ht: Solo a f (fun _:Chin N=> halfBand N) d₀:=by
    let P:= (1/2:ℝ); have hi:= (Crown.ident (badge _) (bail N d₀) a).scale (↑P:ℂ); rw [Complex.norm_real,Real.norm_of_nonneg (show 0≤P by unfold P; norm_num)] at hi; simp_rw [Complex.coe_smul] at hi; exact hi
 have hh: Solo a (B+f) Y d₀:=hp.sub ht
 have hj(x)(p:Guard x d₀) : star (Y (Tulip.profile x))=Y (Tulip.profile x):=by unfold Y hemi_L halfBand; have hx:star (funde j M N (Tulip.profile x))= _:= (he x p).2; rw [star_sub,hx,star_smul,star_one,star_trivial]; rfl
 have ho(s:Sweep N)(x:Pane N)(u':Guard x d₀): Y (Tulip.profile (flashA s x))=realR s true (Y (Tulip.profile x)):=by
    let P₀:=funde j M N (Tulip.profile x); let Q:=funde j M N (Tulip.profile (flashA s x)); have hp:ech s P₀=swapX (detX s.s) Q:= funde_f (castX s) (xtra s.charge) (spinU s.charge s.s) (spinZ s.charge s.s) x j p M d (W N (((le_max_right ..).trans (le_max_right ..)).trans q)) (u'.shrink ((y.trans (min_le_right ..)).trans (min_le_right ..)))
    have hV: star (Y (Tulip.profile x))= _:=hj x u'; let R:= halfBand N
    have he:realR s true (P₀-R)= if (detX s.s) then -ech s P₀+R else ech s P₀-R:=by -- improper uses adjoint
       have hu: star (P₀-R)=P₀-R:=hV
       simp only [realR,ite_true,bolt,hitL,Thera.jazz]; change (if detX s.s then - star (ech s (P₀-R)) else ech s (P₀-R))=_; rw [show star (ech s (P₀-R))=ech s (star (P₀-R)) from (by simp only [ech,singT,win_s,map_star]),hu] -- fix map_star
       unfold ech; cases q:detX s.s <;> simp only [singT,R,halfBand,win_r,win_i,win_l,map_one,map_sub,map_smul,ite_true,ite_false,Bool.false_eq_true] <;> abel -- tune
    change Q-R= realR s true (P₀-R); rw [he,hp]; cases v:detX s.s <;> simp only [swapX,v,ite_false,ite_true,Bool.false_eq_true]; -- tune
    unfold R halfBand; module
 obtain ⟨F,ρ,h⟩:= group_stamp d₀ a Y hh ho
 exact ⟨rimMean F,rimMean_near F Y ρ hj,rimMean_group F h,rimMean_is F⟩
lemma sides_T(a b r s:ℝ)(hr:0≤ r)(hs:0≤ s)(va:0<a)(vb:0<b):∃ e>(0:ℝ),∃ a0>(0:ℝ),∃ C>(0:ℝ),∀ (n:Side)(d:ℝ),0<d→ d≤ e→∀ P:Aim n,P.toll a b r s→ Reef.Cry P→∃ F:Elm n Unit d a0 C, NearL F (fun _=> Moire.bloom P)∧groupShape F:=by
 obtain ⟨A,x,f,g,Y⟩:= Moire.waged 1 hr va; obtain ⟨B,y,h,k,W⟩:=Moire.waged 2 hs vb
 let D:=min A B; have hd:0<D:=lt_min f h; refine ⟨D,hd,D,hd,Tenant.quota^2*(x+y),?_,fun N d w t P l p=>?_⟩
 · have he:0<Tenant.quota:= by unfold Tenant.quota; positivity
   positivity
 let E:=bloom P; have he:Solo D (x+y) E d:= ((axis_down _ _ (Y N P.x l.1) _ w (t.trans (min_le_left ..))).drop (min_le_left ..)).plus ((axis_down _ _ (W N P.y l.2) _ w (t.trans (min_le_right ..))).drop (min_le_right ..))
 exact group_stamp d D E he fun s x _=> prism_x s.charge (castX s) P l p x (spinU s.charge s.s) (spinZ s.charge s.s)
end SliceRoof
end YM.CF.Sour
end
