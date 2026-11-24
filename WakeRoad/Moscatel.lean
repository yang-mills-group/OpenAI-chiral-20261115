import WakeRoad.Boom
import WakeRoad.Ocotea
import Gingham.Ruff.Organza
set_option autoImplicit false
set_option maxHeartbeats 190000
noncomputable section
namespace YM.WakeRoad
open Function Filter Topology NormedSpace Finset Lattice Laurent RG Wilson
open CF CF.Gingham.Ruff CF.Skye CF.Tulip CF.Cube CF.Scree
open scoped ContDiff BigOperators Classical

section
/- recording a quadratic on face coordinates. Keep *symmetric* coefficients,
   nonzero burden can use easy reflected-free eigenvalue test. -/
variable {U:Type}[NormedAddCommGroup U][NormedSpace ℝ U](f:U→ℂ)
def bilux (u v:U):ℂ:=(2:ℝ)⁻¹ • fderiv ℝ (fderiv ℝ f) 0 u v
lemma bi_price {f:U→ ℂ}{c:ℝ}(H:Gallery 2 f c)(u v:U):‖bilux f u v‖ ≤ (c*‖u‖)*‖v‖:= by
 rw [bilux, norm_smul,Real.norm_of_nonneg (by norm_num)]
 let T:= fderiv ℝ (fderiv ℝ f) 0
 have p: ‖T‖ ≤ c := (H.thread.thread 0 (by simp)).value
 refine (mul_le_of_le_one_left (norm_nonneg _) (show (2:ℝ)⁻¹ ≤ 1 from by norm_num)).trans
    (( (T u).le_opNorm v).trans (mul_le_mul_of_nonneg_right ((T.le_opNorm u).trans (mul_le_mul_of_nonneg_right p (norm_nonneg u))) (norm_nonneg v)))
lemma btimes(r s:ℝ)(u v:U):bilux f (r • u) (s • v)=(r*s) • bilux f u v:=by simp [bilux,mul_left_comm,mul_assoc]
lemma moments2 {I:Type*}[Fintype I](u:I→U) :
 quadraticChi f (∑ i,u i) = ∑ i:I,∑ j:I,bilux f (u i) (u j):=by
 unfold quadraticChi bilux; simp_rw [map_sum,_root_.sum_apply,Finset.smul_sum]; rw [sum_comm]
end

open Boom Shells Fan
open CF.Drapes CF.Branch CF.Rill CF.Tenant CF.Peaks
open Fock
attribute [local instance] opCStarAlgebra
variable {N:Side}
local notation "G" => SU.group.Color
abbrev picture (N:Side):=Seat N × PlaqAxes
abbrev Postcard (m:ℕ):= ((↥(box m))× PlaqAxes) × SU.group.ColorIndex
abbrev Paper (m:ℕ):=Postcard m → ℝ
variable (m:ℕ)(o:Seat N)
noncomputable def subject(p: Paper m) : picture N→G:= fun c=> if h: Lattice.lift (c.1-o)∈ box m then WithLp.toLp 2 (fun i=> p ((⟨_,h⟩,c.2),i)) else 0
lemma subject_at(p:Paper m)(x:Seat N)(i:PlaqAxes)(h:lift (x-o)∈box m)(z:SU.group.ColorIndex): subject m o p (x,i) z=p ((⟨_,h⟩,i),z):=by unfold subject; rw [dif_pos h]
lemma subunit (s:Postcard m)(x:Seat N)(i:PlaqAxes):‖subject m o (Pi.single s 1) (x,i)‖ ≤ 1:=by
 by_cases h: lift (x-o)∈box m; swap; · rw [subject,dif_neg h,norm_zero]; norm_num
 let S:=subject m o (Pi.single s 1) (x,i)
 by_cases v:(⟨lift (x-o),h⟩,i)=s.1
 · have p:S=EuclideanSpace.single s.2 1:=by
     ext a; rw [subject_at _ _ _ _ _ h, show EuclideanSpace.single _ (1:ℝ) a= _ from PiLp.single_apply 2 ℝ _ _ _]; by_cases w:a=s.2
     · subst a; simp [v]
     rw [v,if_neg w,Pi.single_eq_of_ne (fun p=>w (congrArg Prod.snd p))]
   change ‖S‖ ≤ 1; rw [p]; exact (show ‖EuclideanSpace.single s.2 (1:ℝ)‖ = ‖(1:ℝ)‖ from PiLp.norm_single _ _ _ _).trans norm_one |>.le
 have p:S=0:=by ext a; rw [subject_at _ _ _ _ _ h, Pi.single_eq_of_ne (fun p=>v (congrArg Prod.fst p))]; rfl
 change ‖S‖ ≤_; rw [p,norm_zero]; norm_num
lemma postcard_tile (p:Paper m)(x:Seat N)(i:PlaqAxes): subject m o p (x,i)=∑ s:Postcard m,p s • subject m o (Pi.single s 1) (x,i):=by
 by_cases h:lift (x-o)∈box m
 · ext q; change _= EuclideanSpace.proj (𝕜:=ℝ) q _; rw [map_sum]; simp only [map_smul]; change _= ∑s:Postcard m,p s * subject m o (Pi.single s 1) (x,i) q; simp_rw [subject_at _ _ _ _ _ h]; let t: Postcard m:=((⟨_,h⟩,i),q); rw [Finset.sum_eq_single t]; · simp [t]
   · intro b _ k; exact (mul_eq_zero_of_right _ (Pi.single_eq_of_ne (Ne.symm k) _))
   simp
 unfold subject; simp [h]

-- clipped pouring. χ is for **unscaled** jet with a dimensional
-- permission δ. we'll rescale later. Use first slot
variable (S:Support (More N))(I:Seal (Seat N))
def exchange (Q:picture N →G): Doub N:=(fun i=> if i.1∈S then income o i Q else 0,0)
abbrev emission (z:Postcard m): Doub N:=exchange o S (subject m o (Pi.single z 1))
lemma wickTerms (p:Paper m): exchange o S (subject m o p)=∑ i:Postcard m,p i • emission m o S i:=by
 apply Prod.ext; swap
 · simp [Prod.snd_sum,emission,exchange]
 have he : subject m o p =∑s:Postcard m,p s • subject m o (Pi.single s 1):=by funext q; exact (postcard_tile m o _ q.1 q.2).trans (by rw [Finset.sum_apply]; rfl)
 rw [he]; simp_rw [exchange,map_sum,map_smul]
 funext i; rw [Prod.fst_sum,Finset.sum_apply]; by_cases v:i.1∈ S <;> simp [v]

variable {I}
lemma emission_fee {y:Site N}{u:Side}(H:Girder y u I)(z: Postcard m):‖emission m (bouton y) I z‖ ≤ 4*Fan.walk u I.card:= by
 rw [Prod.norm_def,max_le_iff]
 have hp:=walk_nn u I.card
 have w:0 ≤ 4*Fan.walk u I.card:=by positivity
 refine ⟨(pi_norm_le_iff_of_nonneg w).mpr fun i=> ?_,(norm_zero).le.trans w⟩ -- norm_zero Coe
 unfold emission exchange
 dsimp only
 split; swap; · exact (norm_zero).le.trans w
 next t=>
 rw [income_stitch]
 refine (income_local_bound _ (H _ t) _ (fun x _ j=> subunit m _ z x j)).trans ?_
 unfold Fan.walk; push_cast; ring_nf; linarith

abbrev blade (u:Side)(n:ℕ):Finset (Postcard m):= Finset.univ.filter fun p=>(p.1.1.val∈ Lattice.box (widthL u+5*n))
private lemma deleted {y:Site N}{u:Side}(h:Girder y u I){i:Postcard m}(v:i∉blade m u I.card): emission m (bouton y) I i=0:= by
 let Q:=subject m (bouton y) (Pi.single i 1)
 have he(t:Edge (Seat N))(l:t.1∈I):income (bouton y) t Q=0:= norm_le_zero_iff.mp ((show ‖income (bouton y) t Q‖ ≤ 4*(↑(widthL u+5*I.card):ℝ)*0 from Boom.income_local_bound (bouton y) (i:=t) (h _ l) Q (C:=0) (fun x p j=>?_)).trans (by simp))
 swap
 · have ht:lift (x-bouton y)∈Lattice.box (widthL u+5*I.card):=Work.E08.lift_mem_box p
   change ‖subject m (bouton y) (Pi.single i 1) (x,j)‖ ≤ 0
   unfold subject; dsimp only; set L := lift (x-bouton y)
   split;swap; · rw [norm_zero]
   next V=>
   have q(z:SU.group.ColorIndex): ((⟨L,V⟩,j),z)≠ i:=fun k=> v (mem_filter.mpr ⟨mem_univ _,(congrArg (fun i:Postcard m=>i.1.1.val) k) ▸ ht⟩)
   simp_rw [Pi.single_eq_of_ne (q _)]
   rw [show WithLp.toLp 2 (fun _:SU.group.ColorIndex=> (0:ℝ)) = (0:G) from rfl,norm_zero]
 refine Prod.ext ?_ rfl; funext t
 change (if t.1∈I then income (bouton y) t Q else 0)=0
 split; · next v=> exact he t v
 rfl

def charade :ℕ:= Fintype.card PlaqAxes * Fintype.card SU.group.ColorIndex * 16
lemma blade_pay (u:Side)(n:ℕ): ((blade m u n).card:ℝ) ≤ charade * Fan.walk u n^4:=by
 let R0:=widthL u+5*n
 let F:=Finset.image (fun i:Postcard m=> ((i.1.1.val,i.1.2),i.2)) (blade m u n)
 have v:(blade m u n).card=F.card:= (card_image_of_injective _ (fun ⟨⟨⟨k,q⟩,i⟩,a⟩ ⟨⟨⟨j,r⟩,w⟩,z⟩ h=>by
     simpa [and_assoc] using (show k=j ∧ i=w ∧ a=z from ⟨congrArg (fun i : (Cover × PlaqAxes) × SU.group.ColorIndex => i.1.1) h, congrArg (fun i : (Cover × PlaqAxes) × SU.group.ColorIndex => i.1.2) h,congrArg Prod.snd h⟩))).symm
 have u:F⊆ (Lattice.box R0 ×ˢ univ) ×ˢ univ:=by intro i t; obtain ⟨i,t₀,rfl⟩:=mem_image.mp t; exact mem_product.mpr ⟨mem_product.mpr ⟨(mem_filter.mp t₀).2,mem_univ _⟩,mem_univ _⟩
 have ht:= (le_trans v.le (card_le_card u)); rw [card_product,card_product,card_univ,card_univ,Corona.box_size] at ht
 refine (Nat.cast_le.mpr ht).trans ?_
 unfold charade; push_cast
 change ((R0:ℝ) + R0+1)^4*_ * _ ≤ _*_*16*(1+(R0:ℝ))^4
 have p:0≤(R0:ℝ):= Nat.cast_nonneg _; have hw: ((R0:ℝ)+R0+1)^4 ≤ (2*(1+(R0:ℝ)))^4:=by gcongr; linarith
 refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hw (Nat.cast_nonneg _)) (Nat.cast_nonneg _)).trans_eq ?_; ring

-- summing coefficients
open CF.Jet CF.Lat CF.Sour
variable {e a c b ρ:ℝ}{y:Site N}{A:Fob N e}{u:Side}(X:Rialto 6 e ρ b)
def ratioAt (f:Doub N→ℂ) (z t:Postcard m):ℂ:=
   bilux f (emission m o S z) (emission m o S t)
lemma ratioLife (f:Doub N→ℂ)(p:Paper m):
   quadraticChi f (exchange o S (subject m o p))=∑ z:Postcard m,∑ t:Postcard m,(p z*p t) • ratioAt m o S f z t:=by rw [wickTerms,moments2]; simp_rw [btimes]; rfl
lemma ratio_price {w:ℝ}(h:Girder y u I)(f:Doub N →ℂ)(H:Gallery 2 f w)(W:0≤w) :
   (∑z:Postcard m,∑t:Postcard m,‖ratioAt m (bouton y) I f z t‖) ≤
   (4^2*charade^2:ℕ)*(w*walk u I.card^10):= by
 let Z:=Postcard m; let R'(z t:Z):=ratioAt m (bouton y) I f z t
 let r:=walk u I.card; let E:=4*r
 have t:0≤E:=mul_nonneg (by positivity) (Fan.walk_nn ..)
 let D:=blade m u I.card
 have h₁(z d:Z): ‖R' z d‖ ≤ w*E^2:= ((bi_price H _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left (emission_fee m h z) W) (emission_fee m h _) (by positivity) (mul_nonneg W t))).trans_eq (by ring)
 have hx(z d:Z)(p:z∉D∨ d∉D) : R' z d=0:=by
    rcases p with p|p <;> unfold R' ratioAt bilux <;> simp only [deleted _ h p,map_zero,_root_.zero_apply,smul_zero]
 change ∑ z:Z,∑ d:Z, ‖R' z d‖ ≤ _
 have d : ∀ z:Z, ∑ t:Z,‖R' z t‖ = ∑ t∈ D,‖R' z t‖:=fun z=> (sum_subset (subset_univ _) (fun i _ p=>by rw [hx _ _ (.inr p),norm_zero])).symm
 simp_rw [d]
 rw [show ∑ z:Z,∑ t∈ D,‖R' z t‖= ∑ z∈D, ∑ t∈ D,‖R' z t‖ from (sum_subset (subset_univ _) fun i _ p'=> sum_eq_zero fun j _=> by rw [hx _ _ (.inl p'),norm_zero]).symm]
 refine (sum_le_sum (fun i _ =>sum_le_sum (fun j _ => h₁ i j))).trans ?_
 simp only [sum_const, nsmul_eq_mul,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
 let v:ℝ:=(charade:ℝ)* r^4; have hz:(D.card:ℝ) ≤ v:= blade_pay m u I.card
 have q0:0≤v:= (Nat.cast_nonneg (α:=ℝ) _).trans hz
 have he : 0 ≤ w*E^2:= mul_nonneg W (sq_nonneg E)
 refine (mul_le_mul hz (mul_le_mul_of_nonneg_right hz he) (mul_nonneg (Nat.cast_nonneg _) he) q0).trans_eq ?_
 unfold v E r; ring

variable {R:Seal (Seat N)→ Prop}
variable (B:Buttons N e R a c A)
def batik (z d:Postcard m):ℂ := ∑ S:Seal (Seat N),ratioAt m o S (hum X (B.mark S)) z d
abbrev Lion :Side→ℝ→ℝ→ℝ:=fun u a c=> (4^2*charade^2:ℕ)* Shells.Interest u a c 10
lemma batik_paid (h:∀ t,R t→ Girder y u t)(p:0<a) : (∑ i:Postcard m,∑ j:Postcard m,‖batik m (bouton y) X B i j‖) ≤ Lion u a c :=by
 unfold batik Lion
 refine (sum_le_sum (fun i _=>sum_le_sum fun j _=> norm_sum_le ..)).trans ?_
 simp_rw [sum_comm (s:=univ (α:=Postcard m)) (t:=univ (α:=Seal (Seat N)))]
 have u(S:Seal (Seat N)):(∑ i:Postcard m,∑ j: Postcard m,‖ratioAt m (bouton y) S (hum X (B.mark S)) i j‖) ≤ (4^2*charade^2:ℕ)*(Gingham.Ruff.Shells.blood (blush (B.cost S)) 1 u S 10):=by
    let G':= Gallery.sub (aria X (B.pass S)) 2 (by norm_num)
    by_cases t: blush (B.cost S)=0
    · rw [t]; unfold Shells.blood; simp only [zero_mul,mul_zero]; apply le_of_eq; refine sum_eq_zero fun i _=> sum_eq_zero fun j _=> ?_
      unfold ratioAt; exact le_antisymm ((bi_price G' ..).trans (by rw [t,zero_mul,zero_mul])) (norm_nonneg _)
    simpa only [Shells.blood,one_mul] using ratio_price m (h _ (apple_positive B _ t)) _ G' (apple_fee ..)
 refine (sum_le_sum (fun i _=> u i)).trans ?_; rw [←Finset.mul_sum]; apply mul_le_mul_of_nonneg_left
 · exact (Shells.tribute B _ p zero_le_one 10).trans (by simp)
 positivity
#print axioms batik_paid

def native (f:tangD N)(p:Postcard m):ℝ:=Boom.collar f (Boom.port o p.1.1.val,p.1.2) p.2
variable {m o}
lemma wear (f:tangD N){x:Seat N}(v:separation o x ≤ m)(j:PlaqAxes) : subject m o (native m o f) (x,j)=Boom.collar f (x,j) :=by
 ext i; rw [subject_at _ _ _ _ _ (Work.E08.lift_mem_box v)]; unfold native; rw [show Boom.port o (lift (x-o))=x from inlet ..]
lemma exchange_ear (f:tangD N){I:Seal (Seat N)}(v:∀ i∈I,separation o i ≤ m){i:Edge (Seat N)}(h:i.1∈I): (exchange o I (subject m o (native m o f))).1 i= income o i (Boom.collar f):=by
 simp only [exchange,h,if_pos]
 apply sub_eq_zero.mp
 rw [←map_sub]; apply norm_le_zero_iff.mp
 refine (Boom.income_local_bound o (v _ h) (subject m o (native m o f) - Boom.collar f) (C:=0) (fun x g j=>?_)).trans ?_
 · change ‖subject m o _ (x,j) - _‖ ≤ _; rw [wear _ g,sub_self,norm_zero]
 simp
include X
lemma ballot (f:tangD N)(hr:0<ρ)(ab:0<a)(hm:2*(m+1)<(More N).val)
  (hs:∀t,R t→∀ i∈t,separation o i ≤ m): quadraticChi (hum X A) (f,0)=∑ i:Postcard m,∑ j:Postcard m,(native m o f i * native m o f j) • batik m o X B i j:=by
 obtain ⟨V,v⟩:= Boom.curl_in o f
 let p:= native m o f
 simp_rw [columnChi X B ab.le (show 3≤6 from by decide), batik, Finset.smul_sum];symm
 simp_rw [sum_comm (s:=univ (α:=Postcard m)) (t:=univ (α:=Seal (Seat N)))]
 refine sum_congr rfl fun S _=>?_
 change (∑ i:Postcard m,∑ j:Postcard m,(p i*p j) • ratioAt m o S _ i j)= _
 let F:=B.mark S; let w:=B.cost S
 let Y:=B.pass S
 rw [← ratioLife]
 by_cases h:blush w=0
 · have u(v:Doub N): quadraticChi (hum X F) v=0:=norm_le_zero_iff.mp ((quadraticChi_small (Gallery.sub (aria X Y) 2 (by decide)) v).trans (by change blush w * _ ≤ 0; rw [h,zero_mul]))
   exact (u _).trans (u (f,0)).symm
 let H:=hs S (apple_positive B S h)
 have y(i:Edge (Seat N))(e:i.1∈ S)(t:i.1+step i.2∈ S): (exchange o S (subject m o p)).1 i = abridge f V i:= (exchange_ear f H e).trans (v i (H _ e) hm).symm
 exact (qAgree Y X _ (abridge f V,0) (fun i e t=> ⟨y i e t,rfl⟩)).trans (qAbridge Y X hr _ _).symm
#print axioms ballot
