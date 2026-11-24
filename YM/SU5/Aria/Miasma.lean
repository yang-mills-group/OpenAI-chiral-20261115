import YM.SU5.Aria.Attenuation
import YM.SU5.FiniteGaugeData.Tower.Alliance
/-!
# Assemble the simultaneous jitter control
Canonical Micromist on all four coordinates. No preferred frame needed for averaging.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Aria
open Set Function Filter Metric
open Germ
open scoped Topology InnerProductSpace
section tide
variable {I:Type*}[DecidableEq I]{Γ:AddSubgroup ℝ}(D: Whisper Γ)
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E]
abbrev PointM (I:Type*) (Γ:AddSubgroup ℝ):= I→Γ
local notation "X"=> (PointM I Γ)
def climate : List I→ Mist (I→Γ)
| [] => .point 0
| i::L=> D.via (fun a=>(climate L).onFn (fun x=> Pi.single i a+x)) -- `single` unification?
lemma held_at (L:List I) (h:L.Nodup){r:ℝ}(p:aloof r D): (climate D L).holds (fun x=>∀ i:I,|(x i:ℝ)| < r):=by
 have z:0<r:=by obtain ⟨a,u⟩:=D.someReach; exact lt_of_le_of_lt (abs_nonneg (a:ℝ)) (D.holds_at.mp p a u)
 have ht(L:List I): (climate D L).holds (fun x=>∀ i:I, i∉L→x i=0):=by
   induction L with
   | nil=>exact fun i _=>rfl
   | cons i L ih=>
     refine (D.hold_via ..).2 (D.solves _ (fun a=>(_root_.YM.CF.Buffered.Afterglow.Tower.Aria.Mist.hold_via ..).2 ((climate D L).promotes ?_ ih))); intro b v q t; obtain ⟨e,h⟩:= (not_or.mp (mt List.mem_cons.mpr t)); change (Pi.single i a + b : I → Γ) q=0; simp [v q h,e]
 induction L with
 | nil=> change ∀ i,|(↑(0:↥Γ):ℝ)| < r; simpa using fun i:I=>z
 | cons i L ih=>
    obtain ⟨u,h⟩:=List.nodup_cons.mp h
    refine (D.hold_via ..).2 (D.promotes ?_ p); intro a h₁; refine (Mist.hold_via ..).2 ((climate D L).promotes ?_ ((climate D L).cradles (ht L) (ih h))); intro b k s; change |((↑((Pi.single i a+b : I → Γ) s)):ℝ)| < r; by_cases e:i=s; subst i; simp only [Pi.add_apply,Pi.single_eq_same,k.1 s u,add_zero]; exact h₁
    apply Eq.mp _ (k.2 s); rw [Pi.add_apply, Pi.single_eq_of_ne (Ne.symm e),zero_add]
lemma climate_mean (i:I)(L:List I)(f:(I→Γ)→E): (climate D (i::L)).mean f=D.mean fun a=> (climate D L).mean (fun x=>f (Pi.single i a + x)):=by rw [climate,D.mean_via]; exact D.mean_congr _ (D.solves _ (fun a=>(climate D L).mean_onFn _ _))
lemma climate_perm (L L':List I)(h:L.Perm L') (f:(I→Γ)→E): (climate D L).mean f=(climate D L').mean f:=by induction h generalizing f with
 | nil=> rfl
 | cons i h ih=>rw [climate_mean,climate_mean]; simp_rw [@ih]
 | trans h w i j=> rw [i,j]
 | swap i j L=> simp_rw [climate_mean]; rw [D.mean_comm D]; congr 1; funext a; congr 1; funext b; congr 1; funext v; rw [add_left_comm] -- tune
end tide
section ropes
variable {B E F : Type*}[NormedAddCommGroup E][NormedSpace ℂ E][NormedAddCommGroup F][NormedSpace ℂ F]
lemma firmly (M:B→ E→L[ℂ] F){v:Filter B} {C:ℝ}(c:0≤C)(h:∀ᶠ i in v, ‖M i‖≤C){x:B→E}{z:E}{a:F}(p:Tendsto (fun i=>M i z) v (𝓝 a))(q:Tendsto x v (𝓝 z)): Tendsto (fun i=>M i (x i)) v (𝓝 a):=by
 have he:Tendsto (fun i=>dist (M i (x i)) a) v (𝓝 0):=by
   have hf:Tendsto (fun i=>C*dist (x i) z + dist (M i z) a) v (𝓝 0):=by simpa using ((q.dist (tendsto_const_nhds (x:=z))).const_mul C).add (p.dist (tendsto_const_nhds (x:=a)))
   apply squeeze_zero' (Eventually.of_forall (fun _=> dist_nonneg)) _ hf
   filter_upwards [h] with i h
   apply (dist_triangle _ (M i z) _).trans; refine add_le_add_left ?_ _
   rw [dist_eq_norm,←map_sub,dist_eq_norm]; exact (M i).le_of_opNorm_le h _ -- right side dist
 exact tendsto_iff_dist_tendsto_zero.mpr he
end ropes
section roles
variable {I T:Type*}[DecidableEq I]{Γ:AddSubgroup ℝ}{H:Hilbert}(D:Whisper Γ)(P:Alliance T Γ H)(z: T→ I) (e: Injective z)(L:List T)
private lemma raw_none (x:T→Γ) (p:∀ i∈ L,x i=0): P.raw L x=ContinuousLinearMap.id ℂ _:=by induction L with | nil=> rfl| cons i l ih=>rw [Alliance.raw_step,p i (List.Mem.head ..),(P.crew i).play_zero,ih (fun j u=> p j (List.Mem.tail _ u))]; rfl
local notation "U" L:max p:max=>P.raw L p
variable (h:L.Nodup)
local notation "ζ" p:max=> p ∘ z
include e h
private lemma onePlay(i:T)(a:↥Γ)(p:i∈ L): P.raw L ((Pi.single (z i) a) ∘ z)= (P.crew i).play a:=by
 induction L with
 | nil=>simp at p
 | cons j L ih=>
    obtain ⟨v,h⟩:=List.nodup_cons.mp h; rcases List.mem_cons.mp p with eq|g
    · subst j; rw [Alliance.raw_step,Function.comp_apply,Pi.single_eq_same,raw_none ..]; rfl
      intro k u; exact Pi.single_eq_of_ne (M:=fun _:I=>↥Γ) (show z k ≠ z i from fun h'=> v (e h' ▸ u)) a -- param
    have hw:z j≠ z i:=fun k=> v ((e k).symm ▸ g); rw [Alliance.raw_step,Function.comp_apply,Pi.single_eq_of_ne hw, (P.crew j).play_zero,ih h g]; rfl
local notation "Id"=> ContinuousLinearMap.id ℂ _
omit e h
def projected (L:List T) : H.Op := L.foldr (fun i (p:H.Op)=> (tide (P.crew i) D).comp p) Id
include e h
lemma projects (G:List T)(g:∀ i∈G,i∈L)(x:H):
    (climate D (G.map z)).mean (fun q=> P.raw L (q∘z) x)=projected D P G x:=by
 induction G with
 | nil=> exact DFunLike.congr_fun (P.raw_zero L) x -- needs 0∘z=0/rfl
 | cons i G ih=>
   rw [List.map_cons,climate_mean,(show projected D P (i::G) x=tide (P.crew i) D (projected D P G x) from rfl),tide_mean]
   refine D.mean_congr _ (D.solves _ fun a=> ?_); -- pull play from singles
   let M:= climate D (G.map z); let B:I → Γ:=Pi.single (z i) a; let Y: H.Op:=(P.crew i).play a
   have hu:∀ t:I→Γ,P.raw L ((B+t)∘z) x=Y (P.raw L (t∘z) x):= fun t=>by rw [show (B+t) ∘ z=(B∘z)+(t∘z) from rfl,P.travelR, onePlay P z e L h i _ (g _ (List.Mem.head ..))]; rfl
   change M.mean (fun t:I→Γ=> P.raw L ((B+t) ∘ z) x)=Y ((projected D P G) x); simp_rw [@hu]; rw [M.mean_linear' (fun t:I→Γ=> P.raw L (t∘z) x),← ih (fun i u=> g i (List.Mem.tail _ u))]
lemma normaliaz (i:I)(u: ∀ t∈L,i≠z t)(x:H) : (climate D (i::L.map z)).mean (fun q=> P.raw L (q∘z) x)=projected D P L x:=by
 rw [climate_mean]; let A:= climate D (L.map z); have t(a:↥Γ)(b:I→Γ): P.raw L ((Pi.single i a+b) ∘ z)=P.raw L (b∘z):=by
   rw [show (Pi.single i a+b) ∘ z=((Pi.single i a)∘z)+(b∘z) from rfl,P.travelR, raw_none _ L]; rfl
   intro j h; rw [Function.comp_apply,Pi.single_eq_of_ne (Ne.symm (u j h))]
 simp_rw [t, D.mean_const]; exact projects D P z e L h L (fun _ p=>p) x
omit e h
lemma translated (M:ℕ→Whisper Γ)(p:∀ i∈ L,∀ x:H,Tendsto (fun n=> tide (P.crew i) (M n) x) atTop (𝓝 ((P.crew i).pi_c x))) (x:H):
    Tendsto (fun i=>projected (M i) P L x) atTop (𝓝 (P.stackS L x)):=by
 induction L with
 | nil=>exact tendsto_const_nhds
 | cons i L ih=>
    exact firmly (fun n:ℕ=>tide (P.crew i) (M n)) (zero_le_one) (Eventually.of_forall fun n=>attenuates ..) (p _ (List.Mem.head ..) _) (ih (fun j u=> p j (List.Mem.tail _ u)))
end roles
end YM.CF.Buffered.Afterglow.Tower.Aria
#print axioms YM.CF.Buffered.Afterglow.Tower.Aria.projects
#print axioms YM.CF.Buffered.Afterglow.Tower.Aria.translated
