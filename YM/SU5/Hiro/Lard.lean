import YM.SU5.Hiro.Crisp
/-! # Exact color structure of the reference at these current insertions. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 320000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Hiro
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Lifted Bilinear Window Skye Emu Onyx Kea Flare Dial
open Cache Glaze
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
variable (R:ℕ){N:Side}{j:ℕ}
open YM.CF.Lamour YM.CF.Velvet
open YM.CF.Lamour.Bridge.Celeste
open YM.CF.Py.Rate.LocalLimit.Papal (Weaver household)
open Ballad
open Twah (DirSpin)
variable {M:Jill.Male}
local notation "ʀ"=>rankG (lake N j M)
variable (o p:Cover)(L G:DirSpin)
abbrev en0 (i:Slot):= (unifyT o L).chargeF (N:=N) (R:=R) i true
abbrev ex0 (i:Slot):= (unifyT o L).chargeF (N:=N) (R:=R) i false
noncomputable def sourceSlot:SU.Slot:=(0,.inr 0)
def dietary (N:Side)(j:ℕ)(M:Jill.Male) :ℂ:= rankG (lake N j M) (en0 R o L sourceSlot) (ex0 R p G sourceSlot)
#check @dietary
local notation "H" a:max b:max l:max g:max=> dietary R a b l g N j M
abbrev alignedα (L:DirSpin)(i:Slot):Emu.Wing:= ⟨dnSpin L.2,i,1⟩
abbrev alignedβ (L:DirSpin)(i:Slot):Emu.Wing:= ⟨upSpin L.1,i,1⟩
lemma in_transcript(i k:Slot): ʀ (en0 R o L i) (ex0 R p G k)=hopF 0 o p (alignedα L i) (alignedβ G k) (Kea.tax emptyC) 1 (lake N j M) R:=by
 rw [clear_canvas]; let T:=lake N j M; change rankG T (nac 0 1 1 _ (o,_)) (nac 0 1 1 _ (p,_))= _; rw [Emu.cat _ _ _ _ _ _ _ _ (by positivity)]; change (if decide (dnSpin L.2 ∉ plusHalf)=decide (upSpin G.1 ∉ plusHalf) then (0:ℂ) else if decide (dnSpin L.2 ∉ plusHalf) then _ else _)= _; rw [decide_eq_true (dn_half L.2),decide_eq_false (show ¬ (upSpin G.1 ∉ plusHalf) from not_not.mpr (up_half _))]; rfl
lemma partial_price (Ht:Even N.val)(i k:Slot): hopF 0 o p (alignedα L i) (alignedβ G k) (Kea.tax emptyC) 1 (lake N j M) R= if i=k then bore (zeroF N) R (o-p) (fun i=>dip j M (tmap (glen (zeroF N) i))) (dnSpin L.2) (upSpin G.1) else 0:=by
 unfold hopF
 let a:=alignedα L i; let t:=alignedβ G k; rw [lake, Emu.mist (too N) 0 o p a t] -- tune
 change (if i=k then bore _ _ (o-p) (trackF _ (lakeP N j M) i) _ _ else _) = _; rw [funext (align_b M Ht i)]; rfl
lemma rank_hint (Ht:Even N.val)(i k:Slot): ʀ (en0 R o L i) (ex0 R p G k)=if i=k then H o p L G else 0:=by
 unfold dietary; simp_rw [in_transcript,partial_price R o p L G Ht,ite_true]
lemma flipcost (i k:Slot): ʀ (ex0 R o L i) (en0 R p G k)= -ʀ (en0 R p G k) (ex0 R o L i):=by unfold rankG; cases a:(ex0 (N:=N) R o L i).1 <;> cases b:(en0 (N:=N) R p G k).1<;> simp
lemma before(i:Slot): (en0 (N:=N) R o L i).1=true:=by change decide (dnSpin _ ∉ plusHalf)=true; exact decide_eq_true (dn_half _)
lemma after_t(i:Slot):(ex0 (N:=N) R o L i).1=false:=by change decide (upSpin _ ∉ plusHalf)=false; exact decide_eq_false (by simpa using up_half L.1)
lemma still(i k:Slot): ʀ (ex0 R o L i) (ex0 R p G k)=0:=if_pos (by rw [after_t,after_t])
lemma calm(i k:Slot): ʀ (en0 R o L i) (en0 R p G k)=0:=if_pos (by rw [before,before])
private lemma seasons {X: Type*} (Z: List X)(L:X→ Reader0 (Single N))(hL:∀ i,KeyT (L i) (tickA N))(M:Jill.Male)(x:Wave (Single N))(p:Sea (spar j M (1:Pane N)) x)(h:1≤j)(t:Kea.Pad j N): alleyR (mateK N) x (rollC (ton ∘ L) Z)=runes (fun i k=> rankG (lake N j M) (L i) (L k)) Z:=by
    have ht:= (pitch M h t.1); let T:= ht.1
    let y:= mateK N; have hv:Sea (Dofu N (field (too N) j M)) x:= coasting t M ▸ p; have Hy:=tickB N
    have hg: skyGlow y 1 x≠0:= shines T x y hv Hy
    change (inner ℂ y x)⁻¹*inner ℂ y (acts (rollC (ton ∘ L) Z) x)=runes (fun a b=> rankG (lake N j M) _ _) Z
    have v:= Emu.frown T Hy hv L (hL) Z;
    unfold pRead skyGlow at v; simp_rw [quant_one,mul_one,act_one,←ht.2] at v; rw [skyGlow,quant_one,act_one] at hg; rw [show inner ℂ y _= _ from v,inv_mul_cancel_left₀ hg]
abbrev sold (i k:Slot):FC (Single N):= ton (en0 R o L k)*ton (ex0 R o L i)
lemma tomato (A:ColorL) : wrapCurrent o L R N A=∑ i:Slot,∑ k:Slot,colorEntry i k A • sold R o L i k:=by
 rw [hold_sum]; apply Finset.sum_congr rfl; intro p _; apply sum_congr rfl; intro q _; apply congrArg ((colorEntry p q A) • ·); rw [sold, en0, ex0, Twah.in_hi, Twah.in_lo, Matrix.smul_mul,Matrix.mul_smul,smul_smul]; have ht: star (gain R)*gain R=(R:ℂ)^3:=by simp only [gain,Complex.star_def,Complex.conj_ofReal]; norm_cast; rw [←sq,Real.sq_sqrt (by positivity)]
 rw [neg_mul,ht]; rfl
variable {x:Wave (Single N)}(H₀:Kea.Pad j N)(h:1≤ j)(e:Sea (spar j M (1:Pane N)) x)
local notation "π"=>alleyR (mateK N) x
include H₀ h e
private lemma letter_cash (i k:Slot): π (sold R o L i k)= if k=i then H o o L L else 0:=by
 let A:Bool→ Reader0 (Single N):=fun b=> if b then en0 R o L k else ex0 R o L i; let Z:List Bool:=[true,false];
 rw [show sold (N:=N) R o L i k=rollC (ton ∘ A) Z from ?_,seasons Z A ?_ M x e h H₀]; rotate_left
 · intro b; cases b <;> exact nac_k ..
 · simp [Z,Fock.rollC,sold,A]
 rw [← rank_hint R o o L L H₀.1 k i]; simp [Z,A,runes,claps,picks,spinC,offer,besideX,cites,Fock.cval,extendsU,beside]
omit H₀ h e in
private lemma gang {X:Type*}(d:X→X→ℂ)(p q r s:X):runes d [p,q,r,s]=d p q*d r s-d p r*d q s+d p s*d q r:=by simp [runes,claps,picks,spinC,offer,besideX,cites,Fock.cval,extendsU,beside]; ring
private lemma letter_dual (i k i' k':Slot) : let A:=sold R o L i k; let B:=sold R p G i' k'; (π) (A*B)= (π A)*(π B)-(if k=i' then H o p L G else 0)*(if k'=i then H p o G L else 0):=by
 intro A B; rw [letter_cash R o L H₀ h e i k,letter_cash R p G H₀ h e i' k']; let Z : List (Fin 4):=[0,1,2,3]; let F:Fin 4→ Reader0 (Single N):=![en0 R o L k, ex0 R o L i,en0 R p G k',ex0 R p G i']; rw [show A*B=rollC (ton ∘ F) Z from ?_, seasons Z F ?_ M x e h H₀]; rotate_left
 · intro k; fin_cases k <;> exact nac_k ..
 · simp [Z,F,Fock.rollC,mul_assoc,A,B,sold]
 unfold Z; rw [gang]; change ʀ (en0 R o L k) (ex0 R o L i) *ʀ (en0 R p G k') (ex0 R p G i')-ʀ (en0 R o L k) (en0 R p G k') *_+ ʀ (en0 R o L k) (ex0 R p G i') * ʀ (ex0 R o L i) (en0 R p G k') = _; rw [flipcost,calm,zero_mul,sub_zero,rank_hint R o o L L H₀.1,rank_hint R p p G G H₀.1,rank_hint R o p L G H₀.1,rank_hint R p o G L H₀.1,mul_neg]; rfl
lemma heldVoid (A:ColorL): π (wrapCurrent o L R N A)=0:=by
 rw [tomato]; simp_rw [map_sum,map_smul,letter_cash R o L H₀ h e, smul_eq_mul, mul_ite,mul_zero,sum_ite_eq',mem_univ,ite_true]; rw [← sum_mul]; exact mul_eq_zero.mpr (Or.inl (walk_trace A))
-- cross product booked *as is*, weight factored via the verified SU Dynkin trace. -/
def diced (N:Side)(j:ℕ)(M:Jill.Male):ℂ:= -60* dietary R o p L G N j M * dietary R p o G L N j M
lemma cherry (A B:ColorL): π (wrapCurrent o L R N A * wrapCurrent p G R N B)= diced R o p L G N j M*(inner ℝ A B:ℝ):=by
 let X:=walkC A; let Y:=walkC B; let v:= H o p L G; let u:= H p o G L
 let α (i k:Slot):= X i k; let β (i k:Slot):= Y i k; have he: π (wrapCurrent o L R N A*wrapCurrent p G R N B)=(π (wrapCurrent o L R N A))*(π (wrapCurrent p G R N B))-∑ i:Slot,∑ k:Slot, α i k*β k i*v*u:=by
    let x(i k:Slot):=sold R o L (N:=N) i k; let y(i k:Slot):=sold (N:=N) R p G i k; let U(i k:Slot):= if i=k then v else 0; let V(i k:Slot):=if i=k then u else 0;
    have hz (i k s t:Slot): α i k*(β s t*(π (x i k*y s t)))=(α i k*π (x i k))*(β s t*π (y s t)) - α i k*β s t*U k s*V t i:=by rw [show π (x i k*y s t) =_ from letter_dual R o p L G H₀ h e i k s t]; unfold U V v u; ring -- tune hygiene π binds x of local name!
    have hp(i k:Slot): (∑ s:Slot,∑ t:Slot,α i k*β s t*U k s*V t i)= α i k*β k i*v*u:=by simp [U,V,mul_ite,ite_mul]
    rw [tomato,tomato]; change π ((∑ i:Slot, ∑ k:Slot, α i k • x i k)*(∑ i:Slot,∑ k:Slot, β i k • y i k))=(_*_)-_; simp_rw [map_sum, sum_mul, mul_sum, Matrix.smul_mul, Matrix.mul_smul, map_sum,map_smul,smul_eq_mul,hz, sum_sub_distrib,hp]; rfl
 rw [he,heldVoid R o L H₀ h e,zero_mul,zero_sub]; simp_rw [←sum_mul]; rw [show ∑ i:Slot,∑ k:Slot,α i k*β k i= _ from (by simpa [Matrix.trace,Matrix.mul_apply,α,β,X,Y] using walk_bill A B)]; unfold diced v u; ring -- rw `show _= _ from` fails meta
end YM.CF.Hiro
#print axioms YM.CF.Hiro.rank_hint
#print axioms YM.CF.Hiro.cherry
