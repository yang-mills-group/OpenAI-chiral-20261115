import YM.SU5.One.Iota

/-! # Chiral signed Banach mark space
Adapted from `Swatch`,`Vitrine`,`LiftMark`. Subsequent PairLens uses this for the additional rank (needed to keep underlying chiral mark products, not just analytical balance of an abstract odd form).
-/
set_option synthInstance.maxSize 30000
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Satin
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry
attribute [local instance] opCStarAlgebra
variable (S:Finset Cover)

variable (K:Calibration)
private lemma vaseOdd (W:List (Tag S)): sing K (W.map (stock S)) = 0 ∨ ∃ (v:ℂ)(r:Finset (Tag S)), W.length = r.card ∧ sing K (W.map (stock S))=v • sing K (tagWord S r):=by
 induction W with
 | nil=> refine Or.inr ⟨1,∅,by simp,?_⟩; simp only [tagWord,List.map_nil,sort_empty,one_smul]
 | cons x W ih=>
    have he:sing K ((x :: W).map (stock S))=Sound.chord K (stock S x)*sing K (W.map (stock S)):=rfl
    rw [he]; rcases ih with ih|⟨c,r,v,e⟩
    · left; rw [ih,mul_zero]
    simp only [e]; have hu:Sound.chord K (stock S x) * c • sing K (tagWord S r)= c • (Sound.chord K (stock S x) *sing K (tagWord S r)):=funext fun i=> funext fun t=> Algebra.mul_smul_comm c ((Sound.chord K (stock S x)) i t) (sing K (tagWord S r) i t); rw [hu]
    have hx(i:Side)(t:Fields (K.c i)): Sound.chord K (stock S x) i t=(velvet S (K.c i)).term x:=by
       change Sound.chord _ _ _ _=thread _ _; unfold Sound.chord thread stock; split <;> rfl
    by_cases h:x∈r
    · left; rw [show Sound.chord _ _ * _ = 0 from ?_,smul_zero]; funext i t; change Sound.chord _ _ _ _*_= 0; rw [hx,spool_sing,velvetTag]; exact (velvet ..).tag_mute r x h
    right; refine ⟨c*Fock.parity x r,insert x r,by rw [List.length_cons,v,card_insert_of_notMem h],?_⟩
    funext i t; simp only [Pi.smul_apply,Pi.mul_apply,hx,spool_sing,velvetTag]; rw [Poly.tag_any (velvet S (K.c i)) r x h, smul_smul,mul_assoc,parity_sq,mul_one]
private lemma trebleSize (u v:Chorus)(h:u.length = v.length): treble u=treble v:=by
 induction u generalizing v with
 | nil=> rw [show v=[] from List.length_eq_zero_iff.mp h.symm]
 | cons i u ih=>
    obtain _ | ⟨j,v⟩:=v
    · simp at h
    rw [Sound.treble,Sound.treble,ih v (by simpa using h)] -- indentation
abbrev Squad (S:Finset Cover)(rank:Bool) := {i:Finset (Tag S)//treble (tagWord S i)=rank}
variable (rank:Bool)
private lemma retailGrade (x: PairsC→ℂ)(u:Chorus)(v:staves u S)(hue_: treble u = rank) : note K x u=0 ∨ ∃ (y:ℂ)(r:Squad S rank),note K x u= y • note K x (tagWord S r.val):=by
 have he(u:Chorus)(g:staves u S): ∃ W:List (Tag S), u=W.map (stock S):=by
    induction u with
    | nil => exact ⟨[],rfl⟩
    | cons i u ih=> let j:Tag S:= ⟨i,g i List.mem_cons_self⟩; obtain ⟨V,p⟩:= ih fun a t=> g a (List.mem_cons_of_mem _ t); exact ⟨j::V,congrArg (i::·) p⟩
 obtain ⟨W,rfl⟩:=he _ v; unfold note; rcases vaseOdd S K W with eq|⟨a,r,h,eq⟩
 · left; rw [eq,mul_zero]
 have ht: Sound.treble (tagWord S r)=rank:= (trebleSize _ (W.map (stock S)) (by simp [tagWord,h])).trans hue_
 exact Or.inr ⟨a,⟨r,ht⟩,by rw [eq]; exact funext fun i=> funext fun t=> Algebra.mul_smul_comm a (scalar K x i t) (sing K (tagWord S r) i t)⟩
lemma steer (x:Purse S)(a:Chorus)(z:ℂ): z • note K x.val a=note K (hue S x z).val a:=by
 funext i t; rw [Pi.smul_apply,Pi.smul_apply,note_v,note_v,show (hue S x z).val _=z*_ from rfl,mul_smul]
lemma circulateAll {x:Family K}(h:InTest K true S rank x):∃ a:Squad S rank → Purse S,x=∑ t:Squad S rank,note K (a t).val (tagWord S t.val):=by
 let Z:Purse S:=⟨0,⟨fun _=>by contradiction,Girt.rite_c _,fun _ _ _ _=>rfl⟩⟩
 have q(u): note K (Z.val) u=0:=by funext i t; rw [note_v]; change (0:ℂ) • _=0; rw [zero_smul]
 have q'(f:Family K)(p:f=0):∃ a:Squad S rank→Purse S,f=∑ t:Squad S rank,note K (a t).val (tagWord S t.val):=⟨fun _=>Z,by simp [q,p]⟩
 refine Submodule.span_induction (p:=fun x _=>∃ a:Squad S rank→Purse S,x=∑ t:Squad S rank,note K (a t).val (tagWord S t.val)) (fun i p=> ?_) (q' _ rfl) ?_ ?_ (whole h)
 · obtain ⟨F,u,v,w,P,rfl⟩:=p; rcases retailGrade S K rank F u w P with e|⟨a,t,h⟩; exact q' _ e
   classical
   let d:Purse S:=⟨F,v⟩
   refine ⟨fun r=> if r=t then hue S d a else Z,?_⟩
   rw [sum_eq_single t,h]; simp only [ite_true]; exact steer S K d _ a
   · intro j _ m; simp only [m,ite_false,q]
   simp
 · rintro i j _ _ ⟨a,rfl⟩ ⟨b,rfl⟩
   let z(t:Squad S rank): Purse S:=⟨(a t).val+(b t).val,⟨fun _=>by contradiction,Girt.kitE _ _ (fun (i j:ℂ)=>i+j) (by fun_prop) (a t).property.env (b t).property.env,fun x y p q=> congrArg₂ (fun (i j:ℂ)=> i+j) ((a t).property.locus _ _ p q) ((b t).property.locus _ _ p q)⟩⟩
   refine ⟨z,?_⟩; change _=∑ t:Squad S rank,note K ((a t).val+(b t).val) _; simp_rw [note_plus,sum_add_distrib]
 rintro i t _ ⟨a,rfl⟩; exact ⟨fun t=>hue S (a t) i, by rw [Finset.smul_sum]; exact sum_congr rfl fun t _=>steer S K (a t) _ i⟩
end YM.CF.Buffered.Afterglow.Satin
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra

variable (S:Finset Cover)(rank:Bool)
abbrev Bazaar := (Satin.Squad S rank) → Pigment S
variable (K : Calibration)

def fresco : Bazaar S rank →ₗ[ℂ] Family K where
  toFun f:= ∑ x:Squad S rank, note K (daub S (f x)) (tagWord S x.val)
  map_add' f g:= by
    simp_rw [Pi.add_apply,show ∀ f g,daub S (f+g)=daub S f+daub S g from fun _ _=>rfl, note_plus,sum_add_distrib]
  map_smul' z f:= by
    change _ = z • ∑ x:Squad S rank,note K (daub S (f x)) (tagWord S x.val)
    rw [Finset.smul_sum]; refine sum_congr rfl fun x _=>?_ ; funext m u; simp only [Pi.smul_apply,note_v]; change (z * _) • _= _; rw [mul_smul]; rfl

lemma fresco_eq (f:Bazaar S rank): fresco S rank K f=∑ x:Squad S rank, note K (daub S (f x)) (tagWord S x.val) := rfl
lemma plaid (f:Bazaar S rank): InTest K true S rank (fresco S rank K f):= by
  rw [fresco_eq]; refine InTest.sum univ _ fun i _=>?_ ; exact (by simpa only [i.property] using note_t K _ (authentic S (f i)) (brand S i.val))
lemma outlined {F:Family K} (h:InTest K true S rank F) : ∃ f:Bazaar S rank, fresco S rank K f=F:=by
  obtain ⟨a,t⟩:= circulateAll S K rank h
  exact ⟨fun i=>pigment S (a i).property, t.symm⟩

def kitB {F:Family K} (h:InTest K true S rank F) : Bazaar S rank := (outlined S rank K h).choose
lemma fresco_kitB {F:Family K} (h:InTest K true S rank F) : fresco S rank K (kitB S rank K h) = F := (outlined S rank K h).choose_spec

def reveal (m:Side) : Bazaar S rank →ₗ[ℂ] Mark (K.c m):=(LinearMap.proj m).comp (fresco S rank K)
lemma revealFresco (m:Side)(f:Bazaar S rank) : fresco S rank K f m=reveal S rank K m f:=rfl
lemma revealSupport (m:Side)(f:Bazaar S rank) : AtSupport rank (region S (K.c m)) (reveal S rank K m f) := (plaid S rank K f).support _
lemma revealSpool (m:Side)(f:Bazaar S rank) (x:Fields (K.c m)) :
    reveal S rank K m f x=∑ i:Squad S rank, daub S (f i) (Prod.map (onC _) (onC _) x) • spool (K.c m) (tagWord S i.val) := by
  rw [←revealFresco,fresco_eq]; simp_rw [Finset.sum_apply,note_v,spool_sing]

abbrev splay (S : Finset Cover)(rank:Bool) : ℝ := Fintype.card (Satin.Squad S rank)
lemma bazaarLe (f:Bazaar S rank) {C:ℝ} (c:0≤C)(h:∀ i x, ‖daub S (f i) x‖ ≤ C) : ‖f‖ ≤ C:= (pi_norm_le_iff_of_nonneg c).2 fun i=> pigmentLe S (f i) c (h i)
lemma revealLe (m:Side)(f:Bazaar S rank)(x:Fields (K.c m)) : ‖reveal S rank K m f x‖ ≤ splay S rank * ‖f‖ := by
  rw [←revealFresco,fresco_eq]; simp_rw [Finset.sum_apply]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=>‖f‖) ?_).trans_eq ?_)
  · exact fun i _=> (pitched K _ _ m x).trans ((daubLe S (f i) _).trans (norm_le_pi_norm ..))
  rw [sum_const,nsmul_eq_mul,card_univ]
lemma frescoLe (m:Side)(f:Bazaar S rank)(x:Fields (K.c m)) : ‖fresco S rank K f m x‖ ≤ splay S rank * ‖f‖ := revealLe ..

variable (N:Side)
open Pastry
open Reed (Fine think)

private lemma nodeCoin (a : Cover)(x:Site N)(h:wrap (More N) a=node x):∃ b:Cover, a=nodeC b ∧ wrap N b=x:=by
  let u:=nodeC (Rush.natural x); let k:= periods (More N) a-periods (More N) u
  let b:= Rush.natural x + N.val • k
  have hp:wrap (More N) a=wrap (More N) u:= by unfold u; rw [←node_of,Rush.nat_true]; exact h
  have he : a=u+(More N).val • k:=by
    have e:= carrying (More N) a; have g:=carrying (More N) u
    unfold k; rw [hp] at e; rw [smul_sub]; calc
    _ = (natural ((wrap (More N)) u)+(More N).val • periods (More N) u) + ((More N).val • periods (More N) a - (More N).val • periods (More N) u) := e.symm.trans (by abel)
    _ = _:= by rw [g]
  have hf:a=nodeC b:=by
    rw [he,show (More N).val= (2:ℕ)*N.val from (mul_comm ..),mul_smul]; unfold u b nodeC; rw [smul_add]; abel
  have g:Injective (@node N):= fun x y e=> (assembly N).embed_injective (add_right_cancel (show _+(1:Site (More N))=_+_ from e))
  exact ⟨b,hf,g (by rw [node_of,←hf]; exact h)⟩

section
variable (K:Calibration)(m:Side)
local notation "n"=> (K.c m)
private lemma mineCraft {b : Bool} {A : FC (Single (K.c m))} (p : Fine (Tset n) (modesIn n (region S n)) b A) :
    ∃ f:Family K, InTest K true S b f ∧ ∀ x, f m x=A:=by
  induction p with
  | empty=> exact ⟨0,.zero,fun _=>rfl⟩
  | one=> exact ⟨1,.one,fun _=>rfl⟩
  | add _ _ ih iu=> obtain ⟨f,h,w⟩:=ih; obtain ⟨g,k,v⟩:=iu; exact ⟨f+g,.add h k,fun x=>congrArg₂ (·+·) (w x) (v x)⟩
  | grow _ _ ih iu=> obtain ⟨f,h,w⟩:=ih; obtain ⟨g,k,v⟩:=iu; exact ⟨f*g,.mul h k,fun x=>congrArg₂ (·*·) (w x) (v x)⟩
  | scale _ z ih=> obtain ⟨f,h,w⟩:=ih; exact ⟨z • f,.smul z h, fun x=> congrArg (z • ·) (w x)⟩
  | seed i p =>
    obtain ⟨⟨x,i⟩,k⟩:=i
    obtain ⟨a,ha,hb⟩:= Finset.mem_image.mp ((modes_at ..).mp p)
    obtain ⟨y,rfl,h⟩:= nodeCoin n a x hb; subst x
    let q:=Lifted.index n y i k
    have hp: q∈Tset n ↔ i∈plusHalf := mem_Tset ..
    let w:= Lifted.winding n y
    have ht:w*w=1:= fee_one _; have he:star w=w:=fee_real _
    by_cases t:i∈plusHalf
    · refine ⟨w • creation K y i k,.smul w (.creator k t ha),fun u=>?_ ⟩; change w • create (w • basisKet q)= _; rw [map_smul,create_put,smul_smul,ht,one_smul]; exact Eq.symm (show (think _).term q = _ from if_pos (hp.2 t))
    refine ⟨(-w) • removal K y i k,.smul (-w) (.remover k t ha),fun u=>?_ ⟩; change (-w) • star (create (w • basisKet q))=_; rw [map_smul,create_put,star_smul,he,smul_smul,neg_mul,ht,neg_one_smul]; exact Eq.symm (show (think _).term q= -takeF q from if_neg (mt hp.mp t))

variable (p: Hosp S (K.c m))
private def pigmentPhaseB (i:Squad S rank):ℂ:=(museum S n p i.val).choose
local notation "w" i:max=> pigmentPhaseB S rank K m p i
local notation "φ" => star (flake (Tset n)ᶜ)
set_option quotPrecheck false

def glasses (i:Squad S rank) : FC (Single (K.c m)) →ₗ[ℂ] ℂ where
  toFun A:= crumb (twist φ A) (i.val.map (occupy S n p)) / w i
  map_add' a b:= by rw [map_add,crumb_add, add_div]
  map_smul' z a:= by rw [twist_scalar, crumb_scale,mul_div_assoc]; rfl

lemma glasses_bounded (i:Squad S rank)(A) : ‖glasses S rank K m p i A‖ ≤ ‖A‖ := by
  have he:‖(w i)‖=1:=(museum S n p i.val).choose_spec.1
  change ‖(_/ _ :ℂ)‖≤ _; rw [norm_div,he,div_one]
  exact (norm_entry _ _ _).trans_eq (twist_norm ..)
lemma glasses_reveal (f: Bazaar S rank) (W: Fields n) (i:Squad S rank): glasses S rank K m p i (reveal S rank K m f W) = daub S (f i) (Prod.map (onC n) (onC n) W) := by
  have he (i:Squad S rank) : ‖(w i)‖=1 ∧ twist φ (spool n (tagWord S i.val)) = w i • poke (i.val.map (occupy S n p)):=by rw [velvetTag]; exact (museum S n p i.val).choose_spec
  rw [revealSpool, map_sum,sum_eq_single i]; swap
  · intro j _ k; rw [map_smul]; unfold glasses; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; rw [(he j).2, crumb_scale,Pastry.chip, if_neg ?_,mul_zero, zero_div, smul_zero]; exact fun e=>k (Subtype.ext (Finset.map_injective (occupy S n p) e.symm))
  swap; · simp
  rw [map_smul]; unfold glasses; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; rw [(he i).2,crumb_scale,Pastry.chip,if_pos rfl,mul_one,div_self (by exact norm_pos_iff.mp (zero_lt_one.trans_eq (he i).1.symm)),smul_eq_mul,mul_one]

lemma glasses_rep {A : FC (Single (K.c m))} (h: Fine (Tset n) (modesIn n (region S n)) rank A):
    A=∑ i:Squad S rank, glasses S rank K m p i A • spool n (tagWord S i.val):=by
  obtain ⟨g,H,u⟩:= mineCraft S K m h
  obtain ⟨f,rfl⟩:= outlined S rank K H
  rw [←u (1,1), revealFresco]; simp_rw [glasses_reveal]; rw [revealSpool]
lemma glasses_readCover (f:Bazaar S rank)(x:PairsC)(i:Squad S rank): glasses S rank K m p i (reveal S rank K m f (replant S n x))= daub S (f i) x:=by
  rw [glasses_reveal]; exact (authentic S (f i)).locus _ _ (tacked S n p _) (tacked S n p _)

variable {f: Mark (K.c m)} (r: Roomy S (K.c m))(t: AtSupport rank (region S (K.c m)) f)

def reup (r: Roomy S (K.c m))(t: AtSupport rank (region S (K.c m)) f): Bazaar S rank := fun i=> pigment S (g:=fun x:PairsC=> glasses S rank K m (Roomy.seats r) i (f (replant S n x))) {
  env := by
    have he:Continuous (glasses S rank K m (Roomy.seats r) i):= LinearMap.continuous_of_finiteDimensional _
    apply Env.along (g:= replant S n) (Girt.pole_w _ _ he t.env) (replant_b S n)
  narrow := fun _=>by contradiction
  locus := fun x y a b=> congrArg _ (t.dep _ _ (tack S n r _ _ a) (tack S n r _ _ b)) }
lemma reveal_reup : reveal S rank K m (reup S rank K m r t)=f:=by
  funext x; rw [revealSpool, glasses_rep S rank K m (Roomy.seats r) (t.allV x)] -- glasses_rep rewrites goal f x; beware dependent
  refine sum_congr rfl fun i _=>?_ ; apply congrArg (fun (z: ℂ)=> z • _); unfold reup; rw [daub_pigment]; apply congrArg _ (t.dep _ _ (untack S n (Roomy.seats r) _) (untack S n (Roomy.seats r) _))
end

lemma bazaarQuote (K:Calibration)(m:Side)(f:Bazaar S rank)(p:Hosp S (K.c m)){C:ℝ}(h:∀ x,‖reveal S rank K m f x‖≤ C): ‖f‖ ≤ C:=by
 apply bazaarLe S rank _ ((norm_nonneg _).trans (h (1,1))); intro i x
 rw [←glasses_readCover S rank K m p]; exact (glasses_bounded S rank K m p i _).trans (h _)

lemma revelation (K:Calibration)(m:Side)(p:Hosp S (K.c m)): Injective (reveal S rank K m):=by
 intro f g h; apply sub_eq_zero.mp; apply norm_le_zero_iff.mp; apply bazaarQuote S rank K m _ p
 intro x; rw [map_sub,h,sub_self]; simp
lemma frescoFaithful (K:Calibration): Injective (fresco S rank K):=by
 obtain ⟨m,h⟩:= (separates K S).exists
 exact fun f g p=> revelation S rank K m ⟨h⟩ (congr_fun p m)
end YM.CF.Buffered.Afterglow.Tapestry
