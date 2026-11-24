import YM.CF.BProof.Floral.Difference
set_option autoImplicit false
noncomputable section
open Function Set Filter Metric Complex MeasureTheory
open scoped Topology NNReal ENNReal
namespace YM.CF.Floral
variable {L:ℝ}
abbrev Points (L:ℝ):= Option (disk L)
abbrev Cost (L:ℝ):=Points L→ℝ→Prop
local notation "Reply"=> ℂ→ℂ -- parens
/-- test either a disc argument itself, or the endpoint difference -/
def pup (x:Points L): (ℂ→ℂ)→ₗ[ℂ]ℂ:=Option.elim x (LinearMap.proj (φ:=fun _:ℂ=>ℂ) (R:=ℂ) (1:ℂ)-LinearMap.proj (0:ℂ)) (fun i=> LinearMap.proj (i:ℂ))
private lemma pup_zero (x:Points L):pup x 0=0:=map_zero _
lemma pups (x:disk L)(f:ℂ→ℂ): pup (some x) f=f x:=rfl
lemma pupd (f:ℂ→ℂ):pup (none:Points L) f=f 1-f 0:=rfl -- needs L

def Rule (Q:Cost L) : Prop := ∃ T:Set (ℂ→ℂ), 0∈T ∧ (∀ i∈T,Hol (disk L) i) ∧ ∀ x c, Q x c ↔ ∀ f∈T,‖pup x f‖ ≤ c
namespace Rule
variable {A B:Cost L}
lemma du (h:Rule A)(p:1<L){c C:ℝ}(u:∀ z:disk L,A (some z) c)(v:c/(L-1)≤C): A none C:=by
 obtain ⟨T,f,g,w⟩:=h; refine (w none C).mpr fun x i=> (norm_chord_le p (g x i) (fun z l=> (w (some ⟨z,l⟩) c).mp (u _) x i)).trans v
lemma mono (h:Rule A)(x:Points L)(a b:ℝ)(p:a≤b): A x a→A x b:=by obtain ⟨S,z,w,t⟩:=h; rw [t,t]; exact fun u i g=> (u i g).trans p
lemma pos (h:Rule A)(x:Points L){a:ℝ}(p:A x a):0≤a:=by obtain ⟨S,z,w,t⟩:=h; simpa using ((t x a).mp p 0 z)
lemma rose (h:Rule A)(k:∀ x c,A x c ↔ B x c):Rule B:= (fun e : A=B=> e ▸ h) (funext (fun x=>funext (fun c=>propext (k x c))))
lemma solo{f:ℂ→ℂ}(h:Hol (disk L) f): Rule fun (x:Points L) c=> ‖pup x f‖≤c:=by
 refine ⟨{0,f},mem_insert ..,fun i g=>?_ ,fun x c=>⟨fun s i g=> ?_,fun p=>p _ (mem_insert_of_mem _ (mem_singleton _))⟩⟩
 · rcases mem_insert_iff.mp g with rfl|g; exact differentiableOn_const (c:=(0:ℂ)); exact eq_of_mem_singleton g ▸ h
 rcases mem_insert_iff.mp g with rfl|g; rw [map_zero,norm_zero]; exact (norm_nonneg _).trans s; exact eq_of_mem_singleton g ▸ s
lemma none_cost (L:ℝ): Rule fun (_:Points L) (c:ℝ)=> 0≤c := (solo (f:=0) (differentiableOn_const (0:ℂ))).rose (by simp only [map_zero,norm_zero, implies_true, iff_self])
lemma max_cost {ι:Type*}{F:ι→ Cost L} (h:∀ i,Rule (F i)): Rule fun x c=> 0≤c∧∀ i,F i x c:=by
 classical
 choose T z g w using h; refine ⟨insert 0 (⋃ i,T i),mem_insert ..,fun i p=>?_,?_⟩
 · rcases mem_insert_iff.mp p with rfl|p; · exact differentiableOn_const (c:=(0:ℂ))
   obtain ⟨j,h⟩:=mem_iUnion.mp p; exact g j i h
 intro x c; simp only [w]
 constructor
 · rintro ⟨hx,h⟩ q hv; rcases mem_insert_iff.mp hv with rfl|hQ; · simpa using hx
   obtain ⟨i,p⟩:=mem_iUnion.mp hQ; exact h i _ p
 intro p; exact ⟨by simpa using p 0 (mem_insert ..),fun i f g=> p f (mem_insert_of_mem _ (mem_iUnion.mpr ⟨i,g⟩))⟩
lemma max_cost' {ι:Type*}[Nonempty ι]{F:ι→ Cost L} (h:∀ i,Rule (F i)):Rule fun x c=>∀ i,F i x c:= (max_cost h).rose fun x _=> ⟨And.right,fun s=> let q:=Classical.arbitrary ι; ⟨(h q).pos x (s q),s⟩⟩
lemma coin (h:Rule A)(r:ℝ)(p:0<r): Rule (fun x c=> ∃ a,A x a ∧ r*a≤c):=by
 obtain ⟨T,i,g,w⟩:=h; refine ⟨(fun f:ℂ→ℂ=>(r:ℂ) • f) '' T, ⟨0,i, smul_zero _ ⟩, fun b ⟨j,k,e⟩=> e ▸ (g j k).const_smul (r:ℂ), ?_ ⟩
 intro x c; simp only [w, Set.forall_mem_image,map_smul,norm_smul,norm_real,Real.norm_of_nonneg p.le]
 constructor; · rintro ⟨a,hx,k⟩ i w; exact (mul_le_mul_of_nonneg_left (hx i w) p.le).trans k
 intro h; exact ⟨c/r,fun i e=> (le_div_iff₀ p).mpr ((mul_comm _ _).trans_le (h e)), by rw [mul_div_cancel₀ _ p.ne']⟩
private lemma angle (z:ℂ):∃ a:ℂ,‖a‖ ≤1 ∧ a*z=(‖z‖:ℂ):=by
 by_cases h:z=0; · exact ⟨0,by simp,by simp [h]⟩
 exact ⟨(‖z‖:ℂ)/z,by rw [norm_div,norm_real,Real.norm_of_nonneg (norm_nonneg _),div_self (norm_pos_iff.mpr h).ne'], div_mul_cancel₀ _ h⟩
lemma sum (h:Rule A)(p:Rule B): Rule (fun x c=>∃ a b,A x a ∧ B x b ∧ a+b≤c):=by
 obtain ⟨T,z,g,H⟩:=h; obtain ⟨S,z',g',Y⟩:=p
 let M: Set (ℂ→ℂ):={f| ∃ i∈T,∃ j∈S,∃ a b:ℂ, ‖a‖≤1∧‖b‖≤1∧ f=a • i+b • j}
 have hp(i j:ℂ→ℂ)(a b:ℂ)(p:i∈T)(u:j∈S)(k:‖a‖≤1)(l:‖b‖≤1): a • i+b • j∈M:=⟨i,p,j,u,a,b,k,l,rfl⟩
 refine ⟨M,?_, fun x ⟨i,v,j,w,a,b,k,l,e⟩=>e ▸ ((g i v).const_smul a).add ((g' j w).const_smul b),?_⟩
 · exact ⟨0,z,0,z',0,0,by simp,by simp,by simp⟩
 intro x c; simp only [H,Y]; constructor
 · rintro ⟨a,b,h,g,t⟩ i ⟨j,u,l,v,k,s,y,w,rfl⟩; rw [map_add,map_smul,map_smul]; apply (norm_add_le ..).trans; rw [norm_smul,norm_smul]; exact (add_le_add ((mul_le_of_le_one_left (norm_nonneg _) y).trans (h j u)) ((mul_le_of_le_one_left (norm_nonneg _) w).trans (g l v))).trans t
 intro h; have ht(i j)(u:i∈T)(v:j∈S): ‖pup x i‖+‖pup x j‖≤c:=by
    obtain ⟨a,z,ga⟩:= angle (pup x i); obtain ⟨b,w,gb⟩:=angle (pup x j); have hp:= h _ (hp i j a b u v z w); rw [map_add,map_smul,map_smul,smul_eq_mul,smul_eq_mul,ga,gb,←ofReal_add,norm_real,Real.norm_of_nonneg (by positivity)] at hp; exact hp
 let J:Set ℝ:=(fun z=>‖pup x z‖) '' T
 have hQ(j)(s:j∈S): c-‖pup x j‖∈upperBounds J :=fun a ⟨i,u,e⟩=> e ▸ le_sub_iff_add_le.mpr (ht i j u s)
 have P:= isLUB_csSup (s:=J) (Set.Nonempty.image _ ⟨0,z⟩) ⟨_,hQ _ z'⟩
 exact ⟨sSup J,c-sSup J,fun i e=> P.1 (mem_image_of_mem _ e), fun j v=> by linarith [P.2 (hQ j v)],by linarith⟩
end Rule
end YM.CF.Floral
