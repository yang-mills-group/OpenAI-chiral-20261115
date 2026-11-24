import YM.SU5.Relativistic.Esthete
import YM.SU5.FiniteGaugeData.Pannier.Centrist
/-!
# The prediction of actual mark-mark factorization

Presumes **only** the products of the baryons (gyre opens and glebe sinks).
If every pair, both of which are already *gauge neutral* with no linking cost borrowed,
with support in the one measuring window, and separated by a paid frame gap
are read as products of their reads, can predict E 1. Factor asserts a product between
*same parity* pair. Not using any fake splitting across θ-colors.
This buys new information even if the marks of different characters are incompatible.
Separation later turns into Footprint-detach. 
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.ScreeV
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Lifted Afterglow Tapestry Branch Tenant Skye Cliplet RG Brace Crest Crest.Sleet Crest.Sleet.UpStart Satin Tower.SlabMark
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
abbrev stripeP : ℕ→Bool
|0=>false
|n+1=>(true.xor (stripeP n))
lemma grows (n k:ℕ) : stripeP (n+k)= (stripeP n).xor (stripeP k):=by induction n with| zero=> rw [zero_add, stripeP, Bool.false_xor]| succ n ih=> rw [Nat.succ_add,stripeP,ih,stripeP,Bool.xor_assoc]

variable {K:Calibration}{α:Type*}(F:α→Buffered.Family K)(l:List α)
noncomputable abbrev rolls (F:α→ Buffered.Family K)(l:List α):= (l.map F).prod
lemma vat (S:Finset Cover)(p:∀ i∈l,InTest K false S true (F i)) :InTest K false S (stripeP l.length) (rolls F l):=by induction l with|nil=>exact .one|cons i l ih=>exact (p i List.mem_cons_self).mul (ih fun i h=> p i (List.mem_cons_of_mem _ h))
lemma vat_even (S:Finset Cover)(p:∀ i∈l,InTest K false S false (F i)) : InTest K false S false (rolls F l):=by induction l with|nil=>exact .one|cons i l ih=>exact (p i List.mem_cons_self).mul (ih fun i h=> p i (List.mem_cons_of_mem _ h))
lemma honestL (u:∀ i,Neutral K (F i)):Neutral K (rolls F l):=by
 intro m g x; induction l with|nil=> exact Eq.symm (map_one _)|cons i l ih=> simp only [rolls,List.map_cons,List.prod_cons,Pi.mul_apply,map_mul,u i m g x]; exact congrArg (_ * ·) ih
noncomputable def floorline (m A d:ℕ)(l:List (XGr m)): Finset Cover:= l.toFinset.image (nodeC ∘ baseX m d A)
abbrev Toes (m d A:ℕ)(K:Calibration)(c:Fin 3) (i:XGr m):= gyre K (baseX m d A i) c
abbrev Spring5(m d A:ℕ)(K:Calibration)(c:Fin 3)(F:Waxy)(i:XGr m):=glebe K (archH A) (baseX m d A i) F A c
def price (E:Buffered.Family K→ℂ)(b:Bool)(f:Buffered.Family K):ℂ:=if b then 0 else E f
-- Stock pitch vertical vacant from gaugeTime points. axis price quantifies multiple ahead.
structure Till (K:Calibration)(D:ℕ)(j:Axis)(t:ℤ)(S T:Finset Cover) : Prop where
  stay (x:Cover)(p:x∈S): x j+K.ℓ+D ≤ ruler K.B*t
  start (x:Cover)(p:x∈T): ruler K.B*t + K.ℓ+D ≤ x j
abbrev zigB (B:Side)(L D:ℕ) := 2*L+2*D+16*B.val
abbrev zig (K:Calibration) := zigB K.B K.ℓ
lemma zig_here (S T:Finset Cover)(D:ℕ) (j:Axis) (s:ℤ) (e:∀ x∈S,x j≤ s)(v:∀ x∈T,s+zig K D≤x j):∃ z:ℤ,Till K D j z S T:=by
 let W:=s+ K.ℓ+D; let V:=ruler K.B; let m:= W/V; have hv:0<V:=ruler_gene _; have he: m*V ≤ W:= Int.ediv_mul_le W hv.ne'
 have ht: W ≤ V*(m+1):=by unfold m; have hx:= Int.emod_lt_of_pos W hv; have ht:= Int.emod_add_mul_ediv W V; rw [mul_add,mul_one]; omega
 refine ⟨m+1,fun x t=> ?_,fun x t=>?_⟩
 · exact le_trans (by unfold W; linarith only [e x t]) ht
 change V*_+_+_ ≤ _; apply le_trans _ (v x t); unfold zig zigB; push_cast; rw [mul_add V, mul_one]; unfold W at he; rw [mul_comm] at he; have hf: 16*(K.B.val:ℤ)=V:=rfl; linarith

-- `Favors`: any predicted split across two neutral baryon arrays
variable {m d A:ℕ}(V:Waxy) (j:Fin 3)(S:Finset Cover)
noncomputable abbrev skim5 := rolls (Toes m d A K j)
noncomputable abbrev glade5 := rolls (Spring5 m d A K j V)
lemma topsB (K:Calibration)(m d A:ℕ)(g:List (XGr m)): InTest K false (floorline m A d g) (stripeP g.length) (rolls (Toes m d A K j) g):= vat _ _ _ (fun i h=> (gyre_T ..).mono (singleton_subset_iff.mpr (mem_image_of_mem (nodeC ∘ baseX m d A) (List.mem_toFinset.mpr h))))
lemma wingB (K:Calibration)(m d A:ℕ)(D:Finset ℤ)(K0:∀ i∈ plusHalf,∀ t:ℤ,t∉D→V i t=0)(g:List (XGr m)): InTest K false (labB m d A V D) (stripeP g.length) (rolls (Spring5 m d A K j V) g):= vat _ _ _ (fun i _=> (glebe_T K (archH A) (baseX m d A i) V A j D K0).mono (via_pass ..))
-- perm rephasing left before right. get price zero on every nonempty toe group

section abstract
variable (K : Calibration) -- lexical reserved
private lemma twistless {b d:Bool}{f g:Buffered.Family K}(h:∃ S,InTest K false S b f)(v:∃ T,InTest K false T d g) :∃ z:ℂ,f*g=z • (g*f):=by
 obtain ⟨S,h⟩:=h; obtain ⟨T,v⟩:=v; refine ⟨Sector.grainB b d,funext fun m=>funext fun x=>?_⟩
 have hs:= ((h.mono (Finset.subset_union_left (s₂:=T))).support m).allV x; have hv:= ((v.mono (Finset.subset_union_right (s₁:=S))).support m).allV x; exact hs.sign_com hv
private lemma swish (G:α→ Buffered.Family K) (U P:List α)(H:∀ i, ∃ S,InTest K false S true (G i))(v:U.Perm P) : ∃ s:ℂ, rolls G U=s • rolls G P:=by induction v with
 | nil=> exact ⟨1,(one_smul ..).symm⟩
 | cons a v ih=> obtain ⟨s,p⟩:=ih; refine ⟨s,?_⟩; rw [rolls,List.map_cons,List.prod_cons]; unfold rolls at p; rw [p]; exact Algebra.mul_smul_comm .. -- direction? rolls other
 | swap i j l=> obtain ⟨s,t⟩:=twistless K (H j) (H i); refine ⟨s,?_⟩; change G j*(G i*_)= s • (G i*(G j*_)); rw [←mul_assoc,t, Algebra.smul_mul_assoc,mul_assoc]
 | trans _ _ a b=> obtain ⟨s,u⟩:=a; obtain ⟨t,p⟩:=b; exact ⟨s*t,by rw [u,p,smul_smul]⟩
end abstract

-- witness type for precise singularity; expose InTest and Cov. include either to toes or to other group. don't admit any charged. wordTicks and Euclidean high estimate.
inductive IsBay (K:Calibration)(m d A:ℕ)(V:Waxy)(i:Fin 3)(W:Finset ℤ)(l:List (XGr m))(F:Buffered.Family K)(S:Finset Cover) : Prop
 | out : F=rolls (Spring5 m d A K i V) l → S=labB m d A V W → IsBay K m d A V i W l F S
 | foot : F=rolls (Toes m d A K i) l → S=floorline m A d l → IsBay K m d A V i W l F S

-- props with bound W on gap unsigned; perm certificate, nonempty. constrain right parity. all first gauge field.
structure Stout (K:Calibration)(m d A:ℕ)(V:Waxy)(i:Fin 3)(D:ℕ)(W:Finset ℤ)(E:Buffered.Family K→ℂ) : Prop where
 isStout: ∃ (L P:List (XGr m))(G:Buffered.Family K)(S:Finset Cover)(j:Axis)(t:ℤ),
    L≠[] ∧ P≠[] ∧ L.Nodup ∧ P.Nodup ∧ stripeP L.length=stripeP P.length ∧
    IsBay K m d A V i W P G S ∧ Till K D j t (floorline m A d L) S ∧
      (let F:=rolls (Toes m d A K i) L; E (F*G) ≠ price E (stripeP L.length) F *price E (stripeP P.length) G)

variable (W:Finset ℤ) (M:ℕ)(E:Buffered.Family K→ℂ)
private lemma separatesX (i j: XGr m)(p:d+d ≥ zig K M){a: Fin 3}(h:(nodeC (baseX m d A i)) a.castSucc < (nodeC (baseX m d A j)) a.castSucc):
    nodeC (baseX m d A i) a.castSucc+zig K M ≤ (nodeC (baseX m d A j)) a.castSucc:=by
 rw [base_left,base_left] at h ⊢
 have hp: driftV m i a + 1 ≤ driftV m j a:= by
    by_contra! p; have hx:=mul_le_mul_of_nonneg_left (show driftV m j a≤ driftV m i a by omega) (show (0:ℤ)≤d by exact_mod_cast Nat.zero_le _); omega
 have ht:= mul_le_mul_of_nonneg_left hp (show 0≤ (d:ℤ) by positivity); rw [mul_add,mul_one] at ht; omega

lemma quench (h:∀ D:Finset Cover,Scopes K D E) (p:d+d ≥ zig K M)(e:0<d)(U: ¬ Stout K m d A V j M W E) :
     ∀ L:List (XGr m), L≠[]→ L.Nodup→ price E (stripeP L.length) (rolls (Toes m d A K j) L)=0 := by
 classical
 suffices ht:∀ k:ℕ,∀ L:List (XGr m), L.length=k→ L≠[]→ L.Nodup → price E (stripeP L.length) (rolls (Toes m d A K j) L)=0 from fun L v w=>ht L.length L rfl v w
 intro k; induction k using Nat.strong_induction_on with
 | h k ih=>
   intro D he_ hu hp; let B:= floorline m A d D; let G:= Toes m d A K j
   by_cases v:stripeP D.length=true; · simp only [price,v,if_true]
   match D with
   | []=> contradiction
   | [i]=> exact (v rfl).elim
   | i::j'::L=>
     let D:= i::j'::L; have hf:i≠j':=fun t=> (List.nodup_cons.mp hp).1 (t ▸ List.mem_cons_self)
     obtain ⟨a,f⟩:= diverge m d A i j' hf; let F(t:XGr m):= nodeC (baseX m d A t) a.castSucc
     have he:F i≠ F j':=by change (d:ℤ)*2 ≤ |F i-F j'| at f; intro p; rw [p,sub_self,abs_zero] at f; omega
     let s:=min (F i) (F j'); let l:=fun i=> decide (F i≤ s); let x:= D.filter l; let y:= D.filter fun i=>!(l i)
     have hx(x':XGr m): x'∈ x ↔ x'∈ D ∧ F x'≤ s:=by simp only [x,l,List.mem_filter, decide_eq_true_eq]
     have hy(x':XGr m): x'∈ y ↔ x'∈D ∧ s<F x':=by simp [y,l]
     obtain ⟨b,t,hb,g,c⟩: ∃ b∈D,F b=s∧∃ c∈D,s<F c:=by
        rcases lt_or_gt_of_ne he with v|v; exact ⟨i,List.mem_cons_self,(min_eq_left v.le).symm,j',by simp [D],(min_le_left ..).trans_lt v⟩; exact ⟨j',by simp [D],(min_eq_right v.le).symm,i,List.mem_cons_self,(min_le_right ..).trans_lt v⟩
     have hx0:x ≠ []:=List.ne_nil_of_mem ((hx _).mpr ⟨t,hb.le⟩)
     have hy0:y≠[]:=List.ne_nil_of_mem ((hy _).mpr c)
     have hpL:D.Perm (x++y):=(List.filter_append_perm l D).symm
     have ht':D.length=x.length+y.length:= (hpL.length_eq).trans List.length_append
     let B₀:=floorline m A d x; let T' :=floorline m A d y
     have hK: stripeP x.length=stripeP y.length:=by
        change ¬stripeP D.length=true at v; rw [ht', grows] at v; cases h:stripeP x.length <;> cases hx:stripeP y.length <;> revert v <;>simp [*]
     have ht(i)(h:i∈x): F i ≤ s:=(hx i|>.1 h).2 -- shadow Perm, rename
     obtain ⟨z,g0⟩:= zig_here (K:=K) B₀ T' M a.castSucc s (fun z u=>by obtain ⟨x,v',rfl⟩:=mem_image.mp u; exact ht x (List.mem_toFinset.mp v')) (fun z u=>by obtain ⟨x,v',rfl⟩:= mem_image.mp u; rw [←hb]; exact separatesX M b x p (hb.trans_lt ((hy x|>.1 (List.mem_toFinset.mp v')).2)))
     have hx': x.Nodup:= hp.filter _; have hy':y.Nodup:=hp.filter _
     let X':=rolls G x; let Y':=rolls G y
     have hF:E (X'*Y')=price E (stripeP x.length) X' *price E (stripeP y.length) Y':=by by_contra u; exact U ⟨x,y,Y',T',a.castSucc,z,hx0,hy0,hx',hy',hK,.foot rfl rfl,g0,u⟩
     rw [ih x.length (by have hz:0< y.length:=List.length_pos_iff.mpr hy0; change D.length = _ at he_; omega) x rfl hx0 hx',zero_mul] at hF -- he_
     have hV: price E (stripeP D.length) (rolls G D)= E (rolls G D):=if_neg v
     obtain ⟨γ,T₀⟩:=swish K G _ _ (fun i=>⟨_,gyre_T ..⟩) hpL -- ht shadow
     change price _ _ (rolls G D)=0
     have hp':rolls G D=γ • (X'*Y'):=T₀.trans (by simp [rolls,X',Y']); rw [hV,hp']; rw [(h (B₀∪T')).scale]; rw [hF,smul_zero]
     · let f:=(topsB j K m d A x).mono (Finset.subset_union_left (s₂:=T')); have w:= (topsB j K m d A y).mono (Finset.subset_union_right (s₁:=B₀)); rw [hK] at f; apply InTest.widen; exact Bool.xor_self _ ▸ f.mul w
end YM.CF.Pannier.Chancel.ScreeV
#print axioms YM.CF.Pannier.Chancel.ScreeV.quench
