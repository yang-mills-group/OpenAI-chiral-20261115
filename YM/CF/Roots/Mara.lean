import YM.CF.Roots.Storm
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Roots
open Function Set Metric Mew MeasureTheory Filter Finset
open scoped Topology ContDiff BigOperators Matrix Classical
variable {I E F N :Type*}[Fintype I][LinearOrder I][NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E][NormedAddCommGroup F][NormedSpace ℂ F][CompleteSpace F]
variable [NormedCommRing N][NormedAlgebra ℂ N][CompleteSpace N]
variable {f g u v:Key I→E}{a b a' b': Key I→N}{s t r:List I}
section storm
variable {J:Type*}[DecidableEq J](σ:I→J)(C: I→ I→ℂ) -- matrix (old index i, new p).
local notation "τ"=> pipe_ζ σ
local notation "wS"=> ψS σ
local notation "Ω"=> fuelΦ σ C
local notation "W"=> Storm_C σ C
lemma kR(t:List I) : (t.map (fun _=>(1:ℂ))).prod=1:=by induction t <;> simp [*]
lemma palateF(i:I)(p:i∉s)(h: River a)(u:River b)(hx:s.Nodup):tipI (a*(b∘dune i)) s=tipI (a*b) s∧ tipI ((b ∘dune i)*a) s=tipI (b*a) s:=by
 -- South simple
 let W':I→ℂ:=fun _=>1; have hz:South W' s b (b ∘dune i):= fun t ht=> (tip_V _ _ fun q=>p (ht.subset q)).trans (by unfold W'; rw [kR,one_smul])
 have hb: South W' s a a:=fun k _=>by unfold W'; rw [kR, one_smul]
 exact ⟨(south_prod h u h (u.stay i) _ hx hb hz _ (List.Sublist.refl _)).trans (by unfold W'; rw [kR,one_smul]),(south_prod u h (u.stay _) h _ hx hz hb _ (List.Sublist.refl _)).trans (by unfold W'; rw [kR,one_smul])⟩
lemma source_D (a u:Key I→ N)(h:River a)(p:River u)(i:I)(j:List I) : tipI (Γcut σ C a i*u) j=∑ k∈ τ i,C k i • tipI (cutI a k*u) j:=by
 have he: Γcut σ C a i*u=(fun x=>∑ k∈τ i,C k i • (cutI a k*u) x):=funext fun x=>by change (_:N)*_= _; unfold Γcut; rw [Finset.sum_mul]; simp only [smul_mul_assoc, Pi.mul_apply]
 rw [he,(tip_bank _ (fun k x=> C k i • (cutI a k*u) x) (fun k _=> River.scale ((h.flow k).mul_T p) _)).2]; simp_rw [tip_C ((h.flow _).mul_T p)]
lemma source_H (a u:Key I→ N)(h:River a)(p:River u)(i:I)(j:List I):tipI (u*Γcut σ C a i) j=∑ k∈ τ i,C k i • tipI (u*cutI a k) j:=by rw [mul_comm]; simp_rw [mul_comm u]; exact source_D σ C a u h p i j
-- primitive step.
lemma ζtip_mul (h:River a)(u:River b)(i:I)(p:wS (i::s)):tipI (a*b) (i::s)=tipI (cutI a i*b) s+tipI (a*cutI b i) s:=by
 obtain ⟨j,x⟩:=List.nodup_cons.mp (uS_b _ p)
 rw [tip_mul h u]; exact congrArg₂ (·+·) ((palateF i j (h.flow i) u x).1) (palateF i j (u.flow i) h x).2
open NormedSpace
lemma ζexp (h:River a)(i:I)(p:wS (i::s)):tipI (exp ∘ a) (i::s)=tipI (cutI a i*(exp ∘ a)) s:=by
 obtain ⟨j,x⟩:=List.nodup_cons.mp (uS_b _ p); rw [sailE h]; exact (palateF i j (h.flow i) (h.exp_V) x).1
lemma Ωψb (h:River a)(u:River b)(i:I)(p:wS (i::s)): Ω (a*b) (i::s)= Ω (Γcut σ C a i*b) s + Ω (a*Γcut σ C b i) s:=by
 rw [Ω_tip _ _ (h.mul_T u)]; refine (rer σ C s ?_).trans (tally_ADD σ C (tipI (Γcut σ C a i*b)) (tipI (a*Γcut σ C b i)) s)
 intro l u'
 change tipI (Γcut σ C (a*b) i) l=_ + _
 have he:tipI (Γcut σ C (a*b) i) l =∑ k∈τ i,C k i • tipI (a*b) (k::l):=by
    rw [(tip_bank _ (fun k x=> C k i • cutI (a*b) k x) (fun k _=> River.scale ((h.mul_T u).flow k) _)).2]; simp_rw [tip_C ((h.mul_T u).flow _)]; rfl
 rw [he,source_D _ _ _ b h u,source_H _ _ _ a u h,←sum_add_distrib]; apply sum_congr rfl; intro j q; have hw:wS (j::l):=by unfold ψS; rw [List.map_cons,u',(mem_filter.mp q).2]; exact p
 rw [ζtip_mul _ h u _ hw,smul_add]
lemma roof_Q(i:I)(h:wS (i::s))(p:t.Sublist s): wS (i::t):= (((List.cons_sublist_cons.mpr p).map σ).nodup h)
lemma roof_e (h:River a)(p:River b)(u:River a')(r:River b')(q:wS s)(x:W s a a')(y:W s b b'): W s (a*b) (a'*b'):=by
 induction s generalizing a a' b b'
 case nil=> intro i q; have hx:= x [] (List.Sublist.refl []); have hy:= y [] (List.Sublist.refl []); rw [List.sublist_nil.mp q]; exact congrArg₂ (·*·) (show a' 0=a 0 from hx) (show b' 0=b 0 from hy)
 case cons j l ih=>
    have hh:=List.sublist_cons_of_sublist j (List.Sublist.refl l); have hz:= (List.nodup_cons.mp (show (σ j:: l.map σ).Nodup from q)).2; let ht:=Storm_C.rim σ C x hh; let hf:=Storm_C.rim σ C y hh
    intro k pS; cases pS with
    | cons _ pU=> exact ih h p u r hz ht hf k pU
    | cons_cons _ pU=>
       have hP:= roof_Q σ j q pU; rw [ζtip_mul _ u r _ hP, Ωψb _ _ h p _ hP]; exact congrArg₂ (·+·) (ih (Γsail σ C h j) p (u.flow j) r hz (cut_l σ C h j x) hf _ pU) (ih h (Γsail σ C p j) u (r.flow j) hz ht (cut_l σ C p j y) _ pU)
lemma Ωψc (h:River a)(i:I)(p:wS (i::s)): Ω (exp∘ a) (i::s)= Ω (Γcut σ C a i*(exp∘ a)) s:=by
 rw [Ω_tip σ C h.exp_V]; let G:=exp ∘a
 refine rer _ _ s (fun l u=>?_); have hp:=h.exp_V
 change tipI (Γcut σ C G i) l = _
 have he:tipI (Γcut σ C G i) l=∑ k∈τ i,C k i • tipI G (k::l):=by
    rw [(tip_bank _ (fun k x=> C k i • cutI G k x) (fun k _=> River.scale (hp.flow k) _)).2]; simp_rw [show ∀ k,tipI (fun x=> C k i • cutI G k x) l=C k i • tipI (cutI G k) l from fun k=>tip_C (hp.flow k) _ l]; rfl
 rw [he,source_D σ C _ _ h hp]; apply sum_congr rfl; intro k v; have hk:wS (k::l):=by unfold ψS; rw [List.map_cons,(mem_filter.mp v).2,u]; exact p
 exact congrArg (C k i • ·) (ζexp _ h _ hk)
lemma root_e(h:River a)(p:River b)(q:wS s)(x:W s a b): W s (exp∘ a) (exp∘ b):=by
 induction s generalizing a b
 case nil=> intro i q; have hx:= x [] (List.Sublist.refl []); rw [List.sublist_nil.mp q]; exact congrArg exp (show b 0=a 0 from hx)
 case cons j l ih=>
    have hz:= (List.nodup_cons.mp (show (σ j:: l.map σ).Nodup from q)).2
    have ih:= ih h p hz (Storm_C.rim σ C x (List.sublist_cons_of_sublist _ (List.Sublist.refl _)))
    intro k pS; cases pS with
    | cons _ pU=> exact ih k pU
    | cons_cons _ pU=>
       have hP:= roof_Q σ j q pU; rw [ζexp _ p _ hP,Ωψc _ _ h _ hP]; exact roof_e σ C (Γsail σ C h _) h.exp_V (p.flow _) p.exp_V hz (cut_l σ C h j x) ih _ pU
end storm
end YM.CF.Roots
