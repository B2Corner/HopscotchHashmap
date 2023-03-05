#include <cstdint>
#include <cstddef>
#include <utility>
#include <new>
#include <iterator>
#include <cmath>

template<typename T>
class RawAllocationVector {
private:
    unsigned char* data_;
    size_t size_; // In objects, not bytes
    size_t capacity_; // In objects, not bytes
public:
    RawAllocationVector() : size_(0), capacity_(1) {
        data_ = new (std::align_val_t(std::alignment_of<T>::value)) unsigned char[sizeof(T)];
    }

    RawAllocationVector(const RawAllocationVector& other) : size_(other.size_), capacity_(other.capacity_) {
        data_ = new (std::align_val_t(std::alignment_of<T>::value)) unsigned char[capacity_ * sizeof(T)];
        T* dataT = reinterpret_cast<T*>(data_);
        for(size_t i = 0; i < size_; i++)
            new (dataT + i) T(reinterpret_cast<T*>(other.data_)[i]);
    }

    RawAllocationVector& operator=(const RawAllocationVector& other) {
        if(&other == this)
            return *this;

        clear();
        delete[] data_;

        size_ = other.size_;
        capacity_ = other.capacity_;

        data_ = new (std::align_val_t(std::alignment_of<T>::value)) unsigned char[capacity_ * sizeof(T)];
        T* dataT = reinterpret_cast<T*>(data_);
        for(size_t i = 0; i < size_; i++)
            new (dataT + i) T(reinterpret_cast<T*>(other.data_)[i]);

        return *this;
    }

    ~RawAllocationVector() {
        clear();

        delete[] data_;
    }

    size_t size() const {
        return size_;
    }

    bool empty() const {
        return size_ == 0;
    };

    void swap(RawAllocationVector& other) {
        std::swap(data_, other.data_);
        std::swap(size_, other.size_);
        std::swap(capacity_, other.capacity_);
    }

    void erase(size_t index) {
        T* dataT = reinterpret_cast<T*>(data_);
        dataT[index].~T();

        if(index != size_ - 1) {
            new (dataT + index) T(dataT[size_ - 1]);
        }
        size_--;
    }

    void push_back(const T& x) {
        if(size_ == capacity_) {
            unsigned char* dataNew = new (std::align_val_t(std::alignment_of<T>::value)) unsigned char[2 * capacity_ * sizeof(T)];
            T* dataT = reinterpret_cast<T*>(data_);
            T* dataNewT = reinterpret_cast<T*>(dataNew);
            for(size_t i = 0; i < size_; i++) {
                new (dataNewT + i) T(dataT[i]);
                dataT[i].~T();
            }
            delete[] data_;
            data_ = dataNew;
            capacity_ *= 2;
        }

        T* dataT = reinterpret_cast<T*>(data_);
        new (dataT + size_) T(x);
        size_++;
    }

    void clear() {
        T* dataT = reinterpret_cast<T*>(data_);
        for(size_t i = 0; i < size_; i++)
            dataT[i].~T();
        size_ = 0;
    }

    T& operator[](size_t index) {
        return reinterpret_cast<T*>(data_)[index];
    }

    const T& operator[](size_t index) const {
        return reinterpret_cast<T*>(data_)[index];
    }

    T* data() {
        return reinterpret_cast<T*>(data_);
    }

    const T* data() const {
        return reinterpret_cast<const T*>(data_);
    }
};

template<class KeyType, class ValueType, class Hash = std::hash<KeyType> > class HashMap {
    template<bool IsConst>
    friend class Iterator;
private:
    enum class ElementLocation {
        NotFound = 0,
        InMainBuffer,
        InOverflow
    };

    Hash hasher_;

    unsigned char* data_;
    uint64_t* hops_;
    uint64_t* occupiedDataPositions_;
    RawAllocationVector<std::pair<const KeyType, ValueType> > overflow_;

    // The current number of actually present elements in the main buffer
    size_t dataSize_;

    // Size of the data buffer
    size_t dataCapacity_;

    static constexpr double LOAD_FACTOR_SHRINK = 0.4;
    static constexpr double LOAD_FACTOR_REHASH = 0.6;
    static constexpr double LOAD_FACTOR_EXPAND = 0.8;

    void setDataPositionOccupied(size_t ind) {
        occupiedDataPositions_[ind / 64] |= ((uint64_t)1 << (ind % 64));
    }

    void setDataPositionFree(size_t ind) {
        occupiedDataPositions_[ind / 64] &= std::numeric_limits<uint64_t>::max() ^ ((uint64_t)1 << (ind % 64));
    }

    bool isDataPositionFree(size_t ind) {
        return ((occupiedDataPositions_[ind / 64] >> (ind % 64)) & 1) == 0;
    }

    // Inserts the provided key-value pair without checking if it was present or not
    std::pair<ElementLocation, size_t> internalInsert(const std::pair<const KeyType, ValueType>& x) {
        size_t start = hasher_(x.first) % dataCapacity_;

        size_t freeIndex = std::numeric_limits<size_t>::max();
        for(size_t i = start; i < dataCapacity_; i++) {
            if(isDataPositionFree(i)) {
                freeIndex = i;
                break;
            }
        }

        std::pair<const KeyType, ValueType>* dataCast = reinterpret_cast<std::pair<const KeyType, ValueType>*>(data_);

        if(freeIndex > start + 63 && freeIndex != std::numeric_limits<size_t>::max()) {
            for(size_t i = freeIndex - 1; i >= start && freeIndex > start + 63 && freeIndex - i < 64; i--) {
                if(hops_[i] == 0) {
                    if(i == start)
                        break;
                    continue;
                }

                int32_t firstBit = __builtin_ctzll(hops_[i]);
                if(i + firstBit < freeIndex) {
                    new (dataCast + freeIndex) std::pair<const KeyType, ValueType>(dataCast[i + firstBit]);
                    dataCast[i + firstBit].~pair();
                    setDataPositionFree(i + firstBit);
                    setDataPositionOccupied(freeIndex);
                    hops_[i] ^= ((uint64_t)1 << firstBit);
                    hops_[i] ^= ((uint64_t)1 << (freeIndex - i));

                    freeIndex = i + firstBit;
                }
                if(i == start)
                    break;
            }
        }
        if(freeIndex > start + 63 || freeIndex == std::numeric_limits<size_t>::max()) {
            overflow_.push_back(x);

            return {ElementLocation::InOverflow, overflow_.size() - 1};
        }

        dataSize_++;
        new (dataCast + freeIndex) std::pair<const KeyType, ValueType>(x);
        setDataPositionOccupied(freeIndex);
        hops_[start] |= ((uint64_t)1 << (freeIndex - start));

        return {ElementLocation::InMainBuffer, freeIndex};
    }

    // Finds the specified key; returns where the element was found and the index
    std::pair<ElementLocation, size_t> internalFind(const KeyType& key) const {
        size_t start = hasher_(key) % dataCapacity_;

        uint64_t hopCur = hops_[start];
        std::pair<const KeyType, ValueType>* dataCast = reinterpret_cast<std::pair<const KeyType, ValueType>*>(data_);
        while(hopCur > 0) {
            int32_t lastBit = __builtin_ctzll(hopCur);
            hopCur ^= (uint64_t)1 << lastBit;

            if(dataCast[start + lastBit].first == key)
                return {ElementLocation::InMainBuffer, start + lastBit};
        }

        for(size_t i = 0; i < overflow_.size(); i++)
            if(overflow_[i].first == key)
                return {ElementLocation::InOverflow, i};

        return {ElementLocation::NotFound, 0};
    }

    void internalRehash(size_t newCapacity) {
        RawAllocationVector<std::pair<const KeyType, ValueType> > overflowOld;
        overflow_.swap(overflowOld);

        uint64_t* hopsNew = new uint64_t[newCapacity];
        for(size_t i = 0; i < newCapacity; i++)
            hopsNew[i] = 0;
        uint64_t* hopsOld = hops_;
        hops_ = hopsNew;

        unsigned char* dataNew = new (std::align_val_t(std::alignment_of<std::pair<const KeyType, ValueType>>::value))
        unsigned char[newCapacity * sizeof(std::pair<const KeyType, ValueType>)];
        unsigned char* dataOld = data_;
        data_ = dataNew;

        delete[] occupiedDataPositions_;
        occupiedDataPositions_ = new uint64_t[(newCapacity + 63) / 64];
        for(size_t i = 0; i < (newCapacity + 63) / 64; i++)
            occupiedDataPositions_[i] = 0;

        size_t oldCapacity = dataCapacity_;
        dataCapacity_ = newCapacity;

        // Move the old elements
        dataSize_ = 0;
        for(size_t i = 0; i < overflowOld.size(); i++)
            internalInsert(overflowOld[i]);

        std::pair<const KeyType, ValueType>* dataOldCast = reinterpret_cast<std::pair<const KeyType, ValueType>*>(dataOld);
        for(size_t i = 0; i < oldCapacity; i++) {
            uint64_t hopCur = hopsOld[i];
            while(hopCur > 0) {
                int32_t lastBit = 63 - __builtin_clzll(hopCur);
                hopCur ^= (int64_t)1 << lastBit;

                internalInsert(dataOldCast[i + lastBit]);
                (dataOldCast[i + lastBit]).~pair();
            }
        }

        delete[] dataOld;
        delete[] hopsOld;
    }

    bool internalOnSizeChanged() {
        double loadFactor = static_cast<double>(dataSize_ + overflow_.size()) / dataCapacity_;
        if(loadFactor >= LOAD_FACTOR_EXPAND || loadFactor <= LOAD_FACTOR_SHRINK) {
            internalRehash(std::max((size_t)1, static_cast<size_t>(std::ceil((dataSize_ + overflow_.size()) / LOAD_FACTOR_REHASH))));
            return true;
        }
        return false;
    }

public:
    template<bool IsConst>
    class Iterator : public std::iterator<std::forward_iterator_tag,
            std::conditional<IsConst, const std::pair<const KeyType, ValueType>, std::pair<const KeyType, ValueType>>,
            void,
            std::conditional<IsConst, const std::pair<const KeyType, ValueType>*, std::pair<const KeyType, ValueType>*>,
            std::conditional<IsConst, const std::pair<const KeyType, ValueType>&, std::pair<const KeyType, ValueType>&>> {
        template<class K, class V, class H>
        friend class HashMap;
    private:
        bool inOverflow_;
        size_t baseIndex_;
        size_t elementIndex_;
        uint64_t hopCur_;

        using HashMapPtrType = typename std::conditional<IsConst, const HashMap<KeyType, ValueType, Hash>*, HashMap<KeyType, ValueType, Hash>*>::type;

        HashMapPtrType hashMap_;

        Iterator(bool inOverflow, size_t index, HashMapPtrType hashMap) : inOverflow_(inOverflow), hashMap_(hashMap) {
            if(inOverflow_) {
                baseIndex_ = 0;
                elementIndex_ = index;
                hopCur_ = 0;
            } else {
                elementIndex_ = index;
                baseIndex_ = index;
                while(baseIndex_ > 0 && (hashMap_->hops_[baseIndex_] & ((uint64_t)1 << (elementIndex_ - baseIndex_))) == 0)
                    baseIndex_--;
                hopCur_ = hashMap_->hops_[baseIndex_];
                if(elementIndex_ != baseIndex_)
                    hopCur_ &= ((uint64_t)1 << (elementIndex_ - baseIndex_)) - 1;
                else
                    hopCur_ = 0;
            }
        }
    public:
        Iterator() : inOverflow_(true), baseIndex_(0), elementIndex_(0), hopCur_(0), hashMap_(nullptr) {
            // Do nothing
        }

        Iterator& operator=(const Iterator& other) {
            inOverflow_ = other.inOverflow_;
            baseIndex_ = other.baseIndex_;
            elementIndex_ = other.elementIndex_;
            hopCur_ = other.hopCur_;
            hashMap_ = other.hashMap_;

            return *this;
        }

        Iterator& operator++() {
            if(inOverflow_) {
                elementIndex_++;
            } else {
                if (hopCur_ == 0) {
                    baseIndex_++;
                    while (baseIndex_ < hashMap_->dataCapacity_ && hashMap_->hops_[baseIndex_] == 0) {
                        baseIndex_++;;
                    }
                    if(baseIndex_ == hashMap_->dataCapacity_) {
                        inOverflow_ = true;
                        baseIndex_ = 0;
                        elementIndex_ = 0;
                        hopCur_ = 0;
                        return *this;
                    } else
                        hopCur_ = hashMap_->hops_[baseIndex_];
                }

                int32_t lastBit = 63 - __builtin_clzll(hopCur_);
                hopCur_ ^= (int64_t) 1 << lastBit;

                elementIndex_ = baseIndex_ + lastBit;
            }
            return *this;
        }

        Iterator operator++(int) {
            Iterator result = *this;
            operator++();
            return result;
        }

        typename std::iterator_traits<Iterator>::value_type::type operator*() {
            if(inOverflow_) {
                return hashMap_->overflow_[elementIndex_];
            } else {
                return reinterpret_cast<std::pair<const KeyType, ValueType>*>(hashMap_->data_)[elementIndex_];
            }
        }

        typename std::iterator_traits<Iterator>::pointer::type operator->() {
            if(inOverflow_) {
                return hashMap_->overflow_.data() + elementIndex_;
            } else {
                return reinterpret_cast<typename std::iterator_traits<Iterator>::pointer::type>(hashMap_->data_) + elementIndex_;
            }
        }

        bool operator==(const Iterator& other) {
            return hashMap_ == other.hashMap_ &&
                   inOverflow_ == other.inOverflow_ && baseIndex_ == other.baseIndex_ && elementIndex_ == other.elementIndex_ && hopCur_ == other.hopCur_;
        }

        bool operator!=(const Iterator& other) {
            return !operator==(other);
        }
    };

    using iterator = Iterator<false>;
    using const_iterator = Iterator<true>;

    HashMap() : hasher_(), dataSize_(0), dataCapacity_(1) {
        data_ = new (std::align_val_t(std::alignment_of<std::pair<const KeyType, ValueType> >::value)) unsigned char[sizeof(std::pair<const KeyType, ValueType>)];
        hops_ = new uint64_t[dataCapacity_];
        occupiedDataPositions_ = new uint64_t[1];
        occupiedDataPositions_[0] = 0;
        hops_[0] = 0;
    }

    explicit HashMap(const Hash& hasher) : hasher_(hasher), dataSize_(0), dataCapacity_(1) {
        data_ = new (std::align_val_t(std::alignment_of<std::pair<const KeyType, ValueType> >::value)) unsigned char[sizeof(std::pair<const KeyType, ValueType>)];
        hops_ = new uint64_t[dataCapacity_];
        occupiedDataPositions_ = new uint64_t[1];
        occupiedDataPositions_[0] = 0;
        hops_[0] = 0;
    }

    template<class InputIt>
    HashMap(InputIt ptr1, InputIt ptr2) : HashMap() {
        while(ptr1 != ptr2) {
            insert(*ptr1);
            ptr1++;
        }
    }

    template<class InputIt>
    HashMap(InputIt ptr1, InputIt ptr2, const Hash& hasher) : hasher_(hasher) {
        data_ = new (std::align_val_t(std::alignment_of<std::pair<const KeyType, ValueType> >::value)) unsigned char[sizeof(std::pair<const KeyType, ValueType>)];
        hops_ = new uint64_t[dataCapacity_];
        occupiedDataPositions_ = new uint64_t[1];
        occupiedDataPositions_[0] = 0;
        hops_[0] = 0;

        while(ptr1 != ptr2) {
            insert(*ptr1);
            ptr1++;
        }
    }

    HashMap(std::initializer_list<std::pair<KeyType, ValueType> > initializers) : HashMap() {
        for(const auto& pair : initializers)
            insert(*reinterpret_cast<const std::pair<const KeyType, ValueType>*>(&pair));
    }

    HashMap(std::initializer_list<std::pair<KeyType, ValueType> > initializers, const Hash& hasher) : hasher_(hasher) {
        data_ = new (std::align_val_t(std::alignment_of<std::pair<const KeyType, ValueType> >::value)) unsigned char[sizeof(std::pair<const KeyType, ValueType>)];
        hops_ = new uint64_t[dataCapacity_];
        occupiedDataPositions_ = new uint64_t[1];
        occupiedDataPositions_[0] = 0;
        hops_[0] = 0;

        for(const auto& pair : initializers)
            insert(pair);
    }

    HashMap(const HashMap& other) : hasher_(other.hasher_), overflow_(other.overflow_), dataSize_(other.dataSize_), dataCapacity_(other.dataCapacity_) {
        hops_ = new uint64_t[dataCapacity_];
        data_ = new (std::align_val_t(std::alignment_of<std::pair<const KeyType, ValueType> >::value)) unsigned char[dataCapacity_ * sizeof(std::pair<const KeyType, ValueType>)];
        occupiedDataPositions_ = new uint64_t[(dataCapacity_ + 63) / 64];
        for(size_t i = 0; i < (dataCapacity_ + 63) / 64; i++)
            occupiedDataPositions_[i] = other.occupiedDataPositions_[i];

        std::pair<const KeyType, ValueType>* dataCast = reinterpret_cast<std::pair<const KeyType, ValueType>*>(data_);
        std::pair<const KeyType, ValueType>* otherDataCast = reinterpret_cast<std::pair<const KeyType, ValueType>*>(other.data_);
        for(size_t i = 0; i < dataCapacity_; i++) {
            hops_[i] = other.hops_[i];

            uint64_t hopCur = hops_[i];
            while(hopCur > 0) {
                int32_t lastBit = 63 - __builtin_clzll(hopCur);
                hopCur ^= (int64_t) 1 << lastBit;

                new(dataCast + i + lastBit) std::pair<const KeyType, ValueType>(otherDataCast[i + lastBit]);
            }
        }
    }

    HashMap& operator=(const HashMap& other) {
        if(&other == this)
            return *this;

        clear();
        delete[] data_;
        delete[] hops_;
        delete[] occupiedDataPositions_;

        dataSize_ = other.dataSize_;
        dataCapacity_ = other.dataCapacity_;
        overflow_ = other.overflow_;
        hops_ = new uint64_t[dataCapacity_];
        data_ = new (std::align_val_t(std::alignment_of<std::pair<const KeyType, ValueType> >::value)) unsigned char[dataCapacity_ * sizeof(std::pair<const KeyType, ValueType>)];
        occupiedDataPositions_ = new uint64_t[(dataCapacity_ + 63) / 64];
        for(size_t i = 0; i < (dataCapacity_ + 63) / 64; i++)
            occupiedDataPositions_[i] = other.occupiedDataPositions_[i];

        std::pair<const KeyType, ValueType>* dataCast = reinterpret_cast<std::pair<const KeyType, ValueType>*>(data_);
        std::pair<const KeyType, ValueType>* otherDataCast = reinterpret_cast<std::pair<const KeyType, ValueType>*>(other.data_);
        for(size_t i = 0; i < dataCapacity_; i++) {
            hops_[i] = other.hops_[i];

            uint64_t hopCur = hops_[i];
            while(hopCur > 0) {
                int32_t lastBit = 63 - __builtin_clzll(hopCur);
                hopCur ^= (int64_t) 1 << lastBit;

                new(dataCast + i + lastBit) std::pair<const KeyType, ValueType>(otherDataCast[i + lastBit]);
            }
        }

        return *this;
    }

    ~HashMap() {
        clear();

        delete[] data_;
        delete[] hops_;
        delete[] occupiedDataPositions_;
    }

    size_t size() const {
        return dataSize_ + overflow_.size();
    }

    bool empty() const {
        return dataSize_ == 0 && overflow_.empty();
    }

    Hash hash_function() const {
        return hasher_;
    }

    void insert(const std::pair<const KeyType, ValueType>& pair) {
        std::pair<ElementLocation, size_t> searchResult = internalFind(pair.first);
        if(searchResult.first != ElementLocation::NotFound)
            return;

        internalInsert(pair);

        // Expand if the load factor became too high
        internalOnSizeChanged();
    }

    void erase(const KeyType& key) {
        std::pair<ElementLocation, size_t> searchResult = internalFind(key);
        if(searchResult.first == ElementLocation::NotFound)
            return;

        if(searchResult.first == ElementLocation::InMainBuffer) {
            dataSize_--;
            size_t start = hasher_(key) % dataCapacity_;
            hops_[start] ^= (uint64_t)1 << (searchResult.second - start);

            std::pair<const KeyType, ValueType>* dataCast = reinterpret_cast<std::pair<const KeyType, ValueType>*>(data_);
            (dataCast[searchResult.second]).~pair();
            setDataPositionFree(searchResult.second);
        } else {
            overflow_.erase(searchResult.second);
        }

        internalOnSizeChanged();
    }

    iterator begin() {
        if(dataSize_ == 0)
            return iterator(true, 0, this);

        for(size_t i = 0; i < dataCapacity_; i++)
            if(hops_[i] != 0)
                return iterator(false, i + (63 - __builtin_clzll(hops_[i])), this);

        return iterator(true, overflow_.size() + 1, this);
    }

    const_iterator begin() const {
        if(dataSize_ == 0)
            return const_iterator(true, 0, this);

        for(size_t i = 0; i < dataCapacity_; i++)
            if(hops_[i] != 0)
                return const_iterator(false, i + (63 - __builtin_clzll(hops_[i])), this);

        return const_iterator(true, overflow_.size() + 1, this);
    }

    iterator end() {
        return iterator(true, overflow_.size(), this);
    }

    const_iterator end() const {
        return const_iterator(true, overflow_.size(), this);
    }

    ValueType& operator[](const KeyType& key) {
        std::pair<ElementLocation, size_t> searchResult = internalFind(key);
        if(searchResult.first == ElementLocation::InMainBuffer)
            return (reinterpret_cast<std::pair<const KeyType, ValueType>*>(data_))[searchResult.second].second;
        else if(searchResult.first == ElementLocation::InOverflow)
            return overflow_[searchResult.second].second;
        else {
            std::pair<ElementLocation, size_t> location = internalInsert({key, ValueType()});

            if(internalOnSizeChanged()) {
                std::pair<ElementLocation, size_t> searchResult2 = internalFind(key);
                if(searchResult2.first == ElementLocation::InMainBuffer)
                    return (reinterpret_cast<std::pair<const KeyType, ValueType>*>(data_))[searchResult2.second].second;
                else
                    return overflow_[searchResult2.second].second;
            }

            if(location.first == ElementLocation::InMainBuffer)
                return (reinterpret_cast<std::pair<const KeyType, ValueType>*>(data_))[location.second].second;
            else
                return overflow_[location.second].second;
        }
    }

    iterator find(const KeyType& key) {
        std::pair<ElementLocation, size_t> searchResult = internalFind(key);
        if(searchResult.first == ElementLocation::NotFound)
            return end();
        return iterator(searchResult.first == ElementLocation::InOverflow, searchResult.second, this);
    }

    const_iterator find(const KeyType& key) const {
        std::pair<ElementLocation, size_t> searchResult = internalFind(key);
        if(searchResult.first == ElementLocation::NotFound)
            return end();
        return const_iterator(searchResult.first == ElementLocation::InOverflow, searchResult.second, this);
    }

    const ValueType& at(const KeyType& key) const {
        std::pair<ElementLocation, size_t> searchResult = internalFind(key);
        if(searchResult.first == ElementLocation::NotFound)
            throw std::out_of_range("Key was not found in the HashTable");
        else if(searchResult.first == ElementLocation::InOverflow)
            return overflow_[searchResult.second].second;
        std::pair<const KeyType, ValueType>* dataCast = reinterpret_cast<std::pair<const KeyType, ValueType>*>(data_);
        return dataCast[searchResult.second].second;
    }

    void clear() {
        overflow_.clear(); // Appropriate destructors will be called automatically

        // Clear the main buffer
        std::pair<const KeyType, ValueType>* dataCast = reinterpret_cast<std::pair<const KeyType, ValueType>*>(data_);
        for(size_t i = 0; i < dataCapacity_; i++) {
            uint64_t hopCur = hops_[i];
            while(hopCur > 0) {
                int32_t lastBit = 63 - __builtin_clzll(hopCur);
                hopCur ^= (int64_t)1 << lastBit;

                (dataCast[i + lastBit]).~pair();
            }
            hops_[i] = 0;
        }
        dataSize_ = 0;
        for(size_t i = 0; i < (dataCapacity_ + 63) / 64; i++)
            occupiedDataPositions_[i] = 0;

        // Shrink back to 1 element
        internalRehash(1);
    }
};
