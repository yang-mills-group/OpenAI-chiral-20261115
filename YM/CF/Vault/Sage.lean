import YM.CF.Vault.Liv
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vault
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Next.Free Laurent Fir Bloch SU Drapes Peaks Dial Tulip Scroll Branch
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 8000
variable (j:ℕ)(L:Side)(ho:Odd L.val)(hj:Even j)(p:1≤j)
variable (b k:Bool)
def firmF(b:Bool)(A:Chop Duel): Chop Duel:= if b then A else fun i _ _ G x=>1-A i G x
def risk (A B C: Chop Duel): Chop Duel:=fun i _ _ G x=> throat (A i G x) (B i G x) (C i G x)
abbrev coast : Chop Male:= mateF (foal j true)
abbrev urban : Chop Male:= mateF (wh j L ho true)
abbrev chalk(k:Bool): Chop Duel:= firmF k (paddle true (coast j))
abbrev umber(k:Bool): Chop Duel:= firmF k (paddle false (urban j L ho))
def zoom (k:Bool): Chop Duel:= risk (chalk j k) (umber j L ho k) (fade j k)
def caveat(k:Bool): Chop Duel:= fun i _ _ G x=> zoom j L ho k i G x+zoom j L ho (!k) i G x
def rust(k:Bool): Chop Duel:= fun i _ _ G x=>chalk j k i G x*(caveat j L ho k i G x)⁻¹ * umber j L ho k i G x
abbrev slackX(k:Bool):Chop Duel:= risk (lendX k) (lendX k) (fade j k)
def rusty(k:Bool): Chop Duel:= fun i _ _ G x=> lobe G k *star (fade j (!k) i G (chargeB x))*lobe G k
-- all periods at zero
section
lemma footrest {N: Side}(M:Male)(p:1≤j): IsStarProjection (skewE j M b N 1):=by
 rw [skew_flat j p,cart_traded (cBar j M.val b p M.property)]
 let F:= bent b j M.val; let T:=plates N F
 have h(k:Momentum)(hp:k∈realCube zone):=b_p b j hp M.property
 have hx:T*T=T:=by unfold T; rw [pilesP]; exact pilesE _ _ fun p hp _=> (h _ hp).1
 have ht:star T=T:=by unfold T; rw [pilesS]; exact pilesE _ _ fun p hp _=>(h _ hp).2
 change IsStarProjection (T ⊗ₖ (1:Op Slot)); exact ⟨(by unfold IsIdempotentElem; rw [op_kron_mul,hx,mul_one]), (by unfold IsSelfAdjoint; rw [op_star_kron,ht,star_one])⟩
include p in
lemma fiat(a:Bool) : Atrest L (mateF (foal j a)):=by
 intro i N F G h; refine ⟨?_, homeT G j _ _ p⟩
 unfold vacantR mateF; rw [still_u,foal]; have ht:=footrest j a (N:=F) i p; let W:=skewE j i a F 1; change IsStarProjection (foot G W); refine ⟨(by unfold IsIdempotentElem; rw [←foot_mul,ht.isIdempotentElem.eq]),?_⟩; unfold IsSelfAdjoint; rw [← foot_s,show star W=W from ht.2]
include ho p in
lemma fiat_j(a:Bool): Atrest L (mateF (wh j L ho a)):=by
 intro i N F G h; refine ⟨?_, board_q G j L ho _ _ h p⟩; unfold vacantR mateF; rw [still_u,wh]; exact whirl _ _ (footrest _ _ (upMale L ho i) p)
include ho p
lemma ucap (a:Bool){N P:Side} (G:Ratio N P)(h:G.count=L) (i:Duel):
 vacantR G i (A:=chalk j a)=vacantR G i.1 (A:=mateF (foal j a)) ∧ vacantR G i (A:=umber j L ho a)=vacantR G i.1 (A:=mateF (wh j L ho a)):=by
 cases a
 · change 1-vacantR G i (A:=paddle true (coast j))= _ ∧1-vacantR G i (A:=paddle false (urban j L ho))= _; rw [pad_f (fiat j L p true) true i G h,pad_f (fiat_j _ _ _ p true) false i G h]; exact ⟨(foil_neg j G true i.1 _).symm,(wh_neg j L ho G true i.1 _).symm⟩ -- order tune
 exact ⟨pad_f (fiat j L p true) true i G h,pad_f (fiat_j j L ho p true) false i G h⟩
include hj
variable (a:Bool){N P:Side} (G:Ratio N P)(h:G.count=L) (i:Duel)
include h
lemma zoom_id: vacantR G i (A:=zoom j L ho a)=Peaks.lake j L ho (@Peaks.cloth j) a i.1 G (vacancyY N P).1:=by
 obtain ⟨hx,hy⟩:= ucap j L ho p a G h i; change vacantR G i *vacantR G i * vacantR G i=_; rw [hx,hy,fade_at j L ho hj G h]; rfl -- tune
omit h in
lemma funds_u : ∀ k,BoxD L (ℒ true) (ℒ true) (chalk j k) ∧ BoxD L (ℒ false) (ℒ false) (umber j L ho k):=by
 obtain ⟨-,A,B⟩:= cup j L ho hj p (canUse j L ho) true
 have hp:=pad_money ho (BoxD.marked A) (fiat j L p _); have ht:=pad_money ho (BoxD.marked B) (fiat_j j L ho p _)
 intro k; cases k; exact ⟨BoxD.one.sub hp,BoxD.one.sub ht⟩; exact ⟨hp,ht⟩
end
include hj p ho
lemma stricter : BoxD L (ℒ false) (ℒ true) (zoom j L ho k):=by obtain ⟨hx,hy⟩:=funds_u j L ho hj p k; exact (hy.chain (fade_cost j L ho hj k)).chain hx
lemma handsome : BoxD L (ℒ true) (ℒ false) (rust j L ho k)∧ Still L (fun G x=>∀ i,IsUnit (caveat j L ho k i G (post x))):=by
 let A:=caveat j L ho k; have he: BoxD L (ℒ false) (ℒ true) A:= (stricter j L ho hj p k).add (stricter j L ho hj p (!k));
 let Q:= halves j L ho (@Peaks.cloth j) k
 obtain ⟨t,h⟩:=seller j L ho hj p k _ (canUse j L ho); let Y:Script Male:= fun i N P G x=> (Q i G x)⁻¹
 have hh:BoxD L (ℒ true) (ℒ false) (fun i:Duel=>@mateF (@Y) i.1):= (BoxD.marked t).reindex Prod.fst -- tune
 obtain ⟨g,kp,l,F⟩:=h
 have hy:Still L (fun G _ => ∀ i:Duel,A i G (vacancyY _ _) * mateF Y i.1 G (vacancyY _ _)=1):=by
    refine ⟨1,one_pos,l,fun {N P} G e hp x t i=>?_⟩; unfold A caveat; change (vacantR G i (A:=zoom j L ho k)+vacantR G i (A:=zoom j L ho (!k))) * _ = _
    rw [zoom_id j L ho hj p k G e,zoom_id j L ho hj p (!k) G e]; change Q i.1 G (vacancyY N P).1*(Q i.1 G (vacancyY N P).1)⁻¹= _; rw [still_u]; exact (Fock.live (F G e hp 1 (crests G g kp) i.1)).1
 obtain ⟨a,h⟩:= overStill he hh hy; obtain ⟨w,p⟩:=funds_u j L ho hj p k; exact ⟨(w.chain a).chain p,h⟩
end YM.CF.Vault
