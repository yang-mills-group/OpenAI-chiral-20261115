import YM.CF.DPress.FD.Geo.Mint
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Finset Cash Bifold Deck Hue Ramp
open scoped Topology BigOperators ENNReal NNReal Classical
variable {n:Side} {q l m F:ℕ} {i j x y:Site n} {c:Geo.ColorT q n}{u:Geo.NormW n}{D:Support n}
namespace Geo
abbrev Sord (D:Support n)(c:ColorT q n)(u:NormW n)(m:ℕ)(x y:Site n):= supportT (hits D c u m x) ∪ supportT (hits D c u m y)
variable (p:UBook l D u)(h: separation x y≤1)
local notation "L"=> Site n
local notation "U"=> u
local notation "X"=> tom D u m
local notation "Y"=> hits D c u m
local notation "S"=> Sord D c u m x y
lemma swapP : S=Sord D c u m y x:=union_comm _ _
lemma sord_held: S⊆D:=union_subset (glowD ..) (glowD ..)
include p h
lemma tard (v: i∈S): separation x i ≤ 4*l∧ separation i y ≤ 4*l:=by
 rcases mem_union.mp v with t|t
 · have he:= cap D u p (gem D c u t); exact ⟨(separation_comm ..).trans_le he.le,(separation_triangle i x y).trans (by omega)⟩
 have he:= cap D u p (gem D c u t); have hp:separation y i<4*l:= (separation_comm ..).trans_lt he; exact ⟨(separation_triangle x y i).trans (by omega),he.le⟩
lemma team (v:i∈ S)(t:j∈ S):close l i j:=by
 have he: separation i x ≤ 4*l:= (separation_comm ..).trans_le (tard p h v).1; have hx:= (tard p h t).1; unfold close s10; exact (separation_triangle i x j).trans (by omega)
private def wpart(D:Support n)(c:ColorT q n)(u:NormW n)(m:ℕ)(x y:L):= (Sord D c u m x y).filter (fun i=>tom D u m x i=m∧tom D u m y i=m)
local notation "W"=> wpart D c u m x y
private lemma pearl (x:L)(h:i∈supportT (Y x))(t:X x j=m): c j ≤ c i:= by
 by_contra! r; have he: m ≤kid D c u m x i:= t.symm.trans_le (kids D c u r); have hp:i∉supportT (Y x):= (by rw [mem_h]; push Not; apply Fin.ext; change min _ (min _ (2*(m-_)))=0; rw [Nat.sub_eq_zero_of_le he]; omega)
 exact hp h
private lemma w_p (t:Tight c l): (W).card≤1:=by
 refine card_le_one.mpr ?_; intro i v j s; obtain ⟨u',vx,vy⟩:=mem_filter.mp v; obtain ⟨t',sx,sy⟩:=mem_filter.mp s; by_contra! r; apply t _ _ r (team p h u' t'); apply le_antisymm ((mem_union.mp t').elim (fun v=>pearl p h x v vx) (fun v=>pearl p h y v vy)) ((mem_union.mp u').elim (fun v=>pearl p h x v sx) (fun v=>pearl p h y v sy)) -- p,h include may require h specific x? signature implicit x,y both! pass.
-- partial centers charged to axes
private def Paddle(x i:L)(u:NormW n)(t:Axis)(m:ℕ):=∃ b:Bool,(pole x i t+lng b (u i)).natAbs ≤ m
lemma feeT (v:i ∈ S \ W): ∃ d:Axis,Paddle x i u d m:=by
 have he: i∈D:=sord_held (mem_sdiff.mp v).1; have hp:separation x i ≤ u i:=by
    rcases mem_union.mp (mem_sdiff.mp v).1 with t|t; · exact (separation_comm x i).trans_le (((tom_v D u).1 (gem D c u t)).2.2.le)
    have gx:separation y i < u i:= (separation_comm y i).trans_lt (((tom_v D u).1 (gem D c u t)).2.2); exact (separation_triangle x y i).trans (by omega)
 have ht: ¬ (X x i=m∧X y i=m):=fun p=> (mem_sdiff.mp v).2 (mem_filter.mpr ⟨(mem_sdiff.mp v).1,p⟩); unfold tom at ht; rw [if_pos he,if_pos he,separation_comm i x] at ht; have hx:= separation_triangle i x y; rw [separation_comm i x] at hx; have hr: u i ≤ separation x i+m:=by omega
 obtain ⟨d,hv,v'⟩:= Finset.exists_mem_eq_sup (s:=univ) univ_nonempty (fun t:Axis=> (pole x i t).natAbs); have hg:separation x i=(pole x i d).natAbs:= (separation_comm ..).trans v'; rw [hg] at hp hr; refine ⟨d,?_⟩; by_cases t:0≤pole x i d; · refine ⟨true,?_⟩; rw [show lng true (u i)= -(u i:ℤ) from rfl]; omega
 refine ⟨false,?_⟩; change (pole x i d+ (u i:ℤ)).natAbs ≤ _; omega
lemma overlap (t:Tight c l)(z:2*s10 l < n.val) (v:∀ i∈D,∀ j∈D,i ≠ j→close l i j→Agree m i j (u i) (u j)): (S).card ≤ 5:=by
 choose f hf using fun (i:L) (t:i∈ S \ W)=> feeT p h t; let A:= S \ W; let ψ(i:L):Axis:= if h:i ∈ A then f i h else 0
 have ht(i:L)(v:i∈A): Paddle x i u (ψ i) m:=by unfold ψ; rw [dif_pos v]; exact hf i v
 have hg:Set.InjOn ψ A:=by
    intro i hi j hj e; obtain ⟨b,k⟩:=ht i hi; obtain ⟨d,l'⟩:=ht j hj; have hy: i∈S:= (mem_sdiff.mp (show i∈ A from hi)).1; have hx: j∈S:= (mem_sdiff.mp (show j∈ A from hj)).1; by_contra P; have hv:=v i (sord_held hy) j (sord_held hx) P (team p h hy hx) (ψ j,b,d)
    unfold Fee at hv; rw [pocket (tard p h hy).1 (tard p h hx).1 (by unfold s10 at z; omega),Pi.sub_apply] at hv; rw [e] at k; dsimp only at hv; omega
 have he:(A.image ψ).card≤4:= (card_le_card (subset_univ _)).trans_eq (by rw [card_univ]; rfl); rw [card_image_of_injOn hg] at he; have hp:W⊆ S:=filter_subset _ _; have hz:A.card+(W).card=(S).card:= card_sdiff_add_card_eq_card hp; have hw:=w_p (m:=m) p h t; omega
end Geo
end YM.CF.DPress.FD
