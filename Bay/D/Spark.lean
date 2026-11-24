import Bay.D.Tune
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff

open Carol Zephyr.Chern Zephyr
variable {N:Side}
local notation "axes4" => List.ofFn (id:Axis→Axis)
-- scatter as sum about cursor y. 
def scatter (x:Site N)(s:Signed)(m:ℕ)(l:List Axis)(y:Site N):Op (Single N):=
   squareSum (fun u=>millQ (x+s.act u)) m l y
lemma glade (x y:Site N)(s:Signed):
   ech (room x s) (millQ (x+s.act y))=millQ (x+y):=by
 rw[←wrap_lift y, wrap_signed,millSt,millSt, ←Carol.gap]
 exact Tye.proM (boxA _) (boxA _).injective _ (γS _) (fun i j h=>Tye.birth_l i j _ _ _ h) _

lemma unshade (x:Site N)(s:Signed)(m:ℕ):
   ech (room x s) (scatter x s m axes4 0)=windmill x m:=by
 let F:Op (Single N) →+ Op (Single N):= { toFun:=ech (room x s),map_add':=fun i j=>by rw[ech,singT,win_a,map_add];rfl, map_zero':=by rw[ech,singT,win_z,map_zero] }
 change F (squareSum _ _ _ _) = squareSum _ _ _ _
 rw[squareMap, show (fun u=>F (millQ (x+s.act u)))= (fun u=>millQ (u+x)) from ?_, square_move, zero_add]
 exact funext fun u=>(glade _ _ _).trans (congrArg millQ (add_comm ..))

variable {K:Scree.Loom N}{m k:ℕ}{X Y M:SOp N}{x:Site N}{p:BudgetPoint}{d a b B W v:ℝ}{s:Signed}

def play(x:Site N)(s:Signed)(m:ℕ)(M:SOp N):SOp N:=
    fun w=>(M w-tickA N)*scatter x s m axes4 0

lemma starline (u:Pane N)
    (p:ech (room x s) (M (profile u))=swapX (detX s) (M (profile (flashA (room x s) u))))
    (q:let V:=profile (flashA (room x s) u); (M V-tickA N)*windmill x m=X V +Y V):
    play x s m M (profile u)= σ s • (skies x X s (profile u)+skies x Y s (profile u)):=by
 let W:=room x s
 have j(A B:Op (Single N)):ech W (A+B)=ech W A + ech W B:=by rw[ech,singT,win_a,map_add];rfl
 let J:=skies x X s (profile u)+skies x Y s (profile u)
 let Z:=M (profile (flashA W u))
 have hz:ech W J=(Z-tickA N)*windmill x m:=by
    unfold J skies;rw[j];unfold W;rw[julius,julius];exact q.symm
 have ht:ech W (play x s m M (profile u))=(swapX (detX s) Z - swapX (detX s) (tickA N))*windmill x m:=by
    have hm:=echTick W; rw[show W.s=s from p_s x] at hm
    rw[←p,←hm,←unshade x s]
    unfold play; rw [ech,singT, win_m,win_l,map_mul,map_sub];rfl -- lhs W rw? 

 have h₁:Injective (ech W):=by intro h l z; have g:=congrArg (ech (W⁻¹)) z;rw [Sour.paceK,Sour.paceK,mul_inv_cancel,beat_x,beat_x] at g; exact g
 change _ = σ s • J
 apply h₁; rw[ht]
 unfold Carol.σ; cases detX s
 · simp[swapX];exact hz.symm
 have he:ech W (-J)= -ech W J:=by
    apply eq_neg_of_add_eq_zero_left
    rw [←j,neg_add_cancel,ech,singT,win_z,map_zero]
 simp only[swapX,if_true, neg_smul,one_smul,he,hz]
 rw[show 1-Z-(1-tickA N)=-(Z-tickA N) from by abel,neg_mul]

lemma spark{δ η:ℝ}{A:StemA N}
    {e:ℝ}(ep:0<e)
    (pt:∀ s:Signed,∀u:Pane N,Guard u e→ech (room x s) (M (profile u))=swapX (detX s) (M (profile (flashA (room x s) u))))
    (q:∀t:Openc _ d,(M t.val-tickA N)*windmill x m=X t.val+Y t.val)
    (h:Clearance p K k d)(t:Trunk (node x) X k a b d)
    (r:Soak (node x) Y a v d)
    (w:Oily a d B W)(g:Temper (node x) A B)
    (l:W*(quota^2*v)≤η)
    (u:∀s:Signed, gem (spout (play x s m M) A) (δ+η)):
    gem (gapX p K x X ∘ Zephyr.Chern.petals A) δ:=by
 have ta:0≤a:= w.hb.le -- tune
 refine sonataGem h (boxSeal t ta) _ fun s=>?_
 have ts:=jul_sells (room x s) r
 rw[pole] at ts
 obtain ⟨hy,z⟩:=rootSpout w g ts
 let J:=room x s; let F:=spout (play x s m M) A
 let T:=spout (skies x Y s) A
 let U:=fun j=>σ s*rayX p K x (skies x X s) (Zephyr.Chern.petals A j)
 have e:U=ᶠ[𝓝 0](fun j=>F j + (-σ s)*T j):=by
   filter_upwards [litAngle (node x) p A,petals_safe A h.dept,petals_safe A ep] with j a b c

   let P:=Zephyr.Chern.petals A j
   have hr:profile (flashA J P) ∈ Openc _ d:=⟨flashA J P,keepC _ _ _ _ b,by simpa only[sub_self,norm_zero] using h.dept⟩
   have he:= starline P (pt s _ c) (q ⟨_,hr⟩)
   unfold U rayX litP F T spout
   simp only [Function.comp_apply]
   rw[box_pass h (boxSeal (highX s t) ta) a (fun _ _ _=>rfl) b,
      he, Matrix.trace_smul,Matrix.trace_add,smul_eq_mul]
   ring
 have hz : Bud T:=hy
 have hu:Bud F:=(u s).1
 have hb:= (hu.bloom.add (hz.bloom.scale (-σ s))).congr e
 change Bud U ∧ δ<_
 refine ⟨hb.1,?_⟩
 change δ<(bud U 2).re
 rw[hb.bud_eq,Pi.add_apply,Pi.smul_apply,Complex.add_re]
 have he:δ+η<(bud F 2).re:=(u s).2
 have hx : -((-σ s) • bud T 2).re ≤ η:=by
    rw [neg_smul,Complex.neg_re,neg_neg]
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_smul,sig_norm,one_mul]
    exact (z 2).trans l
 linarith
end YM.CF.Bay.D
