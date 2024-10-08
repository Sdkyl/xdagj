/*
 * The MIT License (MIT)
 *
 * Copyright (c) 2020-2030 The XdagJ Developers
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */

package io.xdag.consensus;

import io.xdag.Kernel;
import io.xdag.Wallet;
import io.xdag.core.*;
import io.xdag.crypto.Hash;
import io.xdag.crypto.RandomX;
import io.xdag.crypto.RandomXMemory;
import io.xdag.listener.BlockMessage;
import io.xdag.listener.Listener;
import io.xdag.listener.PretopMessage;
import io.xdag.net.ChannelManager;
import io.xdag.net.websocket.ChannelSupervise;
import io.xdag.net.websocket.PoolHandShakeHandler;
import io.xdag.pool.PoolAwardManager;
import io.xdag.utils.BytesUtils;
import io.xdag.utils.XdagRandomUtils;
import io.xdag.utils.XdagSha256Digest;
import io.xdag.utils.XdagTime;
import lombok.Getter;
import lombok.extern.slf4j.Slf4j;
import org.apache.commons.lang3.StringUtils;
import org.apache.commons.lang3.concurrent.BasicThreadFactory;
import org.apache.tuweni.bytes.Bytes;
import org.apache.tuweni.bytes.Bytes32;
import org.apache.tuweni.bytes.MutableBytes;
import org.json.JSONException;
import org.json.JSONObject;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.Objects;
import java.util.Random;
import java.util.concurrent.*;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.AtomicReference;

import static io.xdag.utils.BasicUtils.hash2byte;
import static io.xdag.utils.BasicUtils.keyPair2Hash;
import static io.xdag.utils.BytesUtils.compareTo;
import static io.xdag.utils.BytesUtils.equalBytes;

@Slf4j
public class XdagPow implements PoW, Listener, Runnable {

    private final Kernel kernel;
    protected BlockingQueue<Event> events = new LinkedBlockingQueue<>();
    private static final int NUM_CPU_CORES = Runtime.getRuntime().availableProcessors();
    private volatile boolean isSetMinShare;

    protected Timer timer;
    protected Broadcaster broadcaster;
    // 当前区块
    protected AtomicReference<Block> generateBlock = new AtomicReference<>();
    protected AtomicReference<Bytes32> minShare = new AtomicReference<>();
    protected final AtomicReference<Bytes32> minHash = new AtomicReference<>();
    protected final Wallet wallet;

    protected ChannelManager channelMgr;
    protected Blockchain blockchain;
    protected volatile Bytes32 globalPretop;
    protected PoolAwardManager poolAwardManager;
    protected AtomicReference<Task> currentTask = new AtomicReference<>();
    protected AtomicLong taskIndex = new AtomicLong(0L);
    private boolean isWorking = false;
    private final LinkedBlockingQueue<String> shareQueue = new LinkedBlockingQueue<>(1000000);

    private final ExecutorService timerExecutor = Executors.newSingleThreadExecutor(new BasicThreadFactory.Builder()
            .namingPattern("XdagPow-timer-thread")
            .build());

    private final ExecutorService mainExecutor = Executors.newSingleThreadExecutor(new BasicThreadFactory.Builder()
            .namingPattern("XdagPow-main-thread")
            .build());

    private final ExecutorService broadcasterExecutor = Executors.newSingleThreadExecutor(new BasicThreadFactory.Builder()
            .namingPattern("XdagPow-broadcaster-thread")
            .build());

    private final ThreadLocal<Bytes32StringPair> threadMinHash = ThreadLocal.withInitial(() ->
            new Bytes32StringPair(Bytes32.fromHexString("ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"), "default"));


    ExecutorService consumerGroup = Executors.newFixedThreadPool(NUM_CPU_CORES, new BasicThreadFactory.Builder()
            .namingPattern("XdagPow-handleShares-thread")
            .build());

    protected RandomX randomXUtils;
    private boolean isRunning = false;


    public XdagPow(Kernel kernel) {
        this.kernel = kernel;
        this.blockchain = kernel.getBlockchain();
        this.channelMgr = kernel.getChannelMgr();
        this.timer = new Timer();
        this.broadcaster = new Broadcaster();
        this.randomXUtils = kernel.getRandomx();

        this.poolAwardManager = kernel.getPoolAwardManager();
        this.wallet = kernel.getWallet();

    }

    @Override
    public void start() {
        if (!this.isRunning) {
            this.isRunning = true;
            this.isSetMinShare = false;
            for (int i = 0; i < NUM_CPU_CORES; i++) {
                GetShares getShares = new GetShares();
                getShares.isRunning = true;
                consumerGroup.execute(getShares);
            }
            mainExecutor.execute(this);
            kernel.getPoolAwardManager().start();
            timerExecutor.execute(timer);
            broadcasterExecutor.execute(this.broadcaster);
        }
    }

    @Override
    public void stop() {
        if (isRunning) {
            isRunning = false;
            timer.isRunning = false;
            broadcaster.isRunning = false;
            isSetMinShare = false;
        }
    }

    public void newBlock() {
        log.debug("Start new block generate....");
        long sendTime = XdagTime.getMainTime();
        resetTimeout(sendTime);
        if (randomXUtils != null && randomXUtils.isRandomxFork(XdagTime.getEpoch(sendTime))) {
            if (randomXUtils.getRandomXPoolMemIndex() == 0) {
                randomXUtils.setRandomXPoolMemIndex((randomXUtils.getRandomXHashEpochIndex() - 1) & 1);
            }

            if (randomXUtils.getRandomXPoolMemIndex() == -1) {
                long switchTime0 = randomXUtils.getGlobalMemory()[0] == null ? 0 : randomXUtils.getGlobalMemory()[0].getSwitchTime();
                long switchTime1 = randomXUtils.getGlobalMemory()[1] == null ? 0 : randomXUtils.getGlobalMemory()[1].getSwitchTime();

                if (switchTime0 > switchTime1) {
                    if (XdagTime.getEpoch(sendTime) > switchTime0) {
                        randomXUtils.setRandomXPoolMemIndex(2);
                    } else {
                        randomXUtils.setRandomXPoolMemIndex(1);
                    }
                } else {
                    if (XdagTime.getEpoch(sendTime) > switchTime1) {
                        randomXUtils.setRandomXPoolMemIndex(1);
                    } else {
                        randomXUtils.setRandomXPoolMemIndex(2);
                    }
                }
            }

            long randomXMemIndex = randomXUtils.getRandomXPoolMemIndex() + 1;
            RandomXMemory memory = randomXUtils.getGlobalMemory()[(int) (randomXMemIndex) & 1];

            if ((XdagTime.getEpoch(XdagTime.getMainTime()) >= memory.getSwitchTime()) && (memory.getIsSwitched() == 0)) {
                randomXUtils.setRandomXPoolMemIndex(randomXUtils.getRandomXPoolMemIndex() + 1);
                memory.setIsSwitched(1);
            }
            generateBlock.set(generateRandomXBlock(sendTime));
        } else {
            generateBlock.set(generateBlock(sendTime));
        }
        shareQueue.clear();
    }


    public Block generateRandomXBlock(long sendTime) {
        taskIndex.incrementAndGet();
        Block block = blockchain.createNewBlock(null, null, true, null, XAmount.ZERO);
        block.signOut(wallet.getDefKey());
        // The first 20 bytes of the initial nonce are the node wallet address.
        minShare.set(Bytes32.wrap(BytesUtils.merge(hash2byte(keyPair2Hash(wallet.getDefKey())),
                XdagRandomUtils.nextNewBytes(12))));
        block.setNonce(minShare.get());
        minHash.set(Bytes32.fromHexString("ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"));
        currentTask.set(createTaskByRandomXBlock(block, sendTime));
        // send new Task
        PoolHandShakeHandler.resetShareRateLimiter();
        ChannelSupervise.send2Pools(currentTask.get().toJsonString());
        return block;
    }


    public Block generateBlock(long sendTime) {
        taskIndex.incrementAndGet();
        Block block = blockchain.createNewBlock(null, null, true, null, XAmount.ZERO);
        block.signOut(wallet.getDefKey());
        minShare.set(Bytes32.wrap(BytesUtils.merge(hash2byte(keyPair2Hash(wallet.getDefKey())),
                XdagRandomUtils.nextNewBytes(12))));
        block.setNonce(minShare.get());
        // initial nonce
        minHash.set(block.recalcHash());
        currentTask.set(createTaskByNewBlock(block, sendTime));
        PoolHandShakeHandler.resetShareRateLimiter();
        ChannelSupervise.send2Pools(currentTask.get().toJsonString());
        return block;
    }

    protected void resetTimeout(long timeout) {
        timer.timeout(timeout);
        events.removeIf(e -> e.type == Event.Type.TIMEOUT);
    }

    @Override
    public boolean isRunning() {
        return this.isRunning;
    }

    /**
     * Every time a share sent from a pool is received, it will be recorded here.
     */
    @Override
    public void receiveNewShare(String share, String hash, long taskIndex, String poolTag) {

        if (!this.isRunning) {
            return;
        }
        if (currentTask.get() == null) {
            log.info("Current task is empty");
        } else if (currentTask.get().getTaskIndex() == taskIndex && Objects.equals(hash,
                currentTask.get().getTask()[0].getData().toUnprefixedHexString())) {
            onNewShare(Bytes32.wrap(Bytes.fromHexString(share)), poolTag);
        } else {
            log.debug("Task index error or preHash error. Current task is {} ,but pool sends task index is {}",
                    currentTask.get().getTaskIndex(), taskIndex);
        }
    }

    public void receiveNewPretop(Bytes pretop) {
        // make sure the PoW is running and the main block is generating
        if (!this.isRunning || !isWorking) {
            return;
        }

        // prevent duplicate event
        if (globalPretop == null || !equalBytes(pretop.toArray(), globalPretop.toArray())) {
            log.debug("update global pretop:{}", Bytes32.wrap(pretop).toHexString());
            globalPretop = Bytes32.wrap(pretop);
            events.add(new Event(Event.Type.NEW_PRETOP, pretop));
        }
    }

    protected void onNewShare(Bytes32 share, String poolTag) {
        try {
            Task task = currentTask.get();
            Bytes32 hash;
            // if randomx fork
            if (kernel.getRandomx().isRandomxFork(task.getTaskTime())) {
                MutableBytes taskData = MutableBytes.create(64);

                taskData.set(0, task.getTask()[0].getData());// preHash
                taskData.set(32, share);// share
                // Calculate hash
                hash = Bytes32.wrap(kernel.getRandomx()
                        .randomXPoolCalcHash(taskData, taskData.size(), task.getTaskTime()).reverse());
            } else {
                XdagSha256Digest digest = new XdagSha256Digest(task.getDigest());
                hash = Bytes32.wrap(digest.sha256Final(share.reverse()));
            }
            if (compareTo(hash.toArray(), 0, 32, minHash.get().toArray(), 0, 32) < 0) {
                minHash.set(hash);
                minShare.set(share);
                Bytes32StringPair poolInfo = threadMinHash.get();
                poolInfo.setKey(share);
                poolInfo.setValue(poolTag);
            }
        } catch (Exception e) {
            log.error(e.getMessage(), e);
        }
    }

    protected void setNonce(String poolTag, Bytes32 share) throws IOException {
        Task task = currentTask.get();
        Bytes32 hash;
        // if randomx fork
        if (kernel.getRandomx().isRandomxFork(task.getTaskTime())) {
            MutableBytes taskData = MutableBytes.create(64);

            taskData.set(0, task.getTask()[0].getData());// preHash
            taskData.set(32, share);// share
            // Calculate hash
            hash = Bytes32.wrap(kernel.getRandomx()
                    .randomXPoolCalcHash(taskData, taskData.size(), task.getTaskTime()).reverse());
        } else {
            XdagSha256Digest digest = new XdagSha256Digest(task.getDigest());
            hash = Bytes32.wrap(digest.sha256Final(share.reverse()));
        }
        synchronized (minHash) {
            if (compareTo(hash.toArray(), 0, 32, minHash.get().toArray(), 0, 32) < 0) {
                minHash.set(hash);
                minShare.set(share);
                Block b = generateBlock.get();
                b.setNonce(minShare.get());
                if (StringUtils.isAsciiPrintable(poolTag)) {
                    byte[] data = poolTag.getBytes(StandardCharsets.UTF_8);
                    byte[] safeRemark = new byte[32];
                    Arrays.fill(safeRemark, (byte) 0);
                    System.arraycopy(data, 0, safeRemark, 0, Math.min(data.length, 32));
                    b.getInfo().setRemark(safeRemark);
                }
            }
        }
    }


    protected void onTimeout() {
        isSetMinShare = true;
        Block b = generateBlock.get();
        // stop generate main block
        isWorking = false;
        if (b != null) {
            Block newBlock = new Block(new XdagBlock(b.toBytes()));
            log.debug("Broadcast locally generated blockchain, waiting to be verified. block hash = [{}]", newBlock.getHash().toHexString());
            // add new block and broadcast the new block
            kernel.getBlockchain().tryToConnect(newBlock);
            Bytes32 currentPreHash = Bytes32.wrap(currentTask.get().getTask()[0].getData());
            poolAwardManager.addAwardBlock(minShare.get(), currentPreHash, newBlock.getHash(), newBlock.getTimestamp());
            BlockWrapper bw = new BlockWrapper(newBlock, kernel.getConfig().getNodeSpec().getTTL());
            broadcaster.broadcast(bw);
        }
        isWorking = true;
        // start generate main block
        newBlock();
        isSetMinShare = false;
    }

    protected void onNewPreTop() {
        isSetMinShare = true;
        log.debug("Receive New PreTop");
        newBlock();
        isSetMinShare = false;
    }

    /**
     * Create a RandomX task
     */
    private Task createTaskByRandomXBlock(Block block, long sendTime) {
        Task newTask = new Task();
        XdagField[] task = new XdagField[2];
        RandomXMemory memory = randomXUtils.getGlobalMemory()[(int) randomXUtils.getRandomXPoolMemIndex() & 1];
        Bytes32 preHash = Hash.sha256(block.getXdagBlock().getData().slice(0, 480));
        // task[0]=preHash
        task[0] = new XdagField(preHash.mutableCopy());
        // task[1]=taskSeed
        task[1] = new XdagField(MutableBytes.wrap(memory.getSeed()));
        newTask.setTask(task);
        newTask.setTaskTime(XdagTime.getEpoch(sendTime));
        newTask.setTaskIndex(taskIndex.get());
        return newTask;
    }

    /**
     * Created original task, now deprecated
     */
    private Task createTaskByNewBlock(Block block, long sendTime) {
        Task newTask = new Task();

        XdagField[] task = new XdagField[2];
        task[1] = block.getXdagBlock().getField(14);
//        byte[] data = new byte[448];
        MutableBytes data = MutableBytes.create(480);

//        System.arraycopy(block.getXdagBlock().getData(), 0, data, 0, 448);
        data.set(0, block.getXdagBlock().getData().slice(0, 480));

        XdagSha256Digest currentTaskDigest = new XdagSha256Digest();
        try {
            currentTaskDigest.sha256Update(data);
            byte[] state = currentTaskDigest.getState();
            task[0] = new XdagField(MutableBytes.wrap(state));
            currentTaskDigest.sha256Update(block.getXdagBlock().getField(14).getData());
        } catch (IOException e) {
            log.error(e.getMessage(), e);
        }
        newTask.setTask(task);
        newTask.setTaskTime(XdagTime.getEpoch(sendTime));
        newTask.setTaskIndex(taskIndex.get());
        newTask.setDigest(currentTaskDigest);
        return newTask;
    }


    @Override
    public void run() {
        log.info("Main PoW start ....");
        timer.timeout(XdagTime.getEndOfEpoch(XdagTime.getCurrentTimestamp() + 64));
        // init pretop
        globalPretop = null;
        while (this.isRunning) {
            try {
                Event ev = events.poll(10, TimeUnit.MILLISECONDS);
                if (ev == null) {
                    continue;
                }
                switch (ev.getType()) {
                    case TIMEOUT -> {
                        if (kernel.getXdagState() == XdagState.SDST || kernel.getXdagState() == XdagState.STST
                                || kernel.getXdagState() == XdagState.SYNC) {
                            onTimeout();
                        }
                    }
                    case NEW_PRETOP -> {
                        if (kernel.getXdagState() == XdagState.SDST || kernel.getXdagState() == XdagState.STST
                                || kernel.getXdagState() == XdagState.SYNC) {
                            onNewPreTop();
                        }
                    }
                    default -> {
                    }
                }
            } catch (InterruptedException e) {
                log.error(e.getMessage(), e);
            } catch (Exception e) {
                throw new RuntimeException(e);
            }
        }
    }

    @Override
    public void onMessage(io.xdag.listener.Message msg) {
        if (msg instanceof BlockMessage message) {
            BlockWrapper bw = new BlockWrapper(new Block(new XdagBlock(message.getData().toArray())),
                    kernel.getConfig().getNodeSpec().getTTL());
            broadcaster.broadcast(bw);
        }
        if (msg instanceof PretopMessage message) {
            receiveNewPretop(message.getData());
        }
    }

    public static class Event {

        @Getter
        private final Type type;
        private final Object data;
        private Object channel;

        public Event(Type type) {
            this(type, null);
        }

        public Event(Type type, Object data) {
            this.type = type;
            this.data = data;
        }

        public Event(Type type, Object data, Object channel) {
            this.type = type;
            this.data = data;
            this.channel = channel;
        }

        @SuppressWarnings("unchecked")
        public <T> T getData() {
            return (T) data;
        }

        @SuppressWarnings("unchecked")
        public <T> T getChannel() {
            return (T) channel;
        }

        @Override
        public String toString() {
            return "Event [type=" + type + ", data=" + data + "]";
        }

        public enum Type {
            /**
             * Received a timeout signal.
             */
            TIMEOUT,
            /**
             * Received a new pretop message.
             */
            NEW_PRETOP,
            /**
             * Received a new largest diff message.
             */
            NEW_DIFF,
        }
    }

    public class Timer implements Runnable {

        private long timeout;
        private boolean isRunning = false;

        @Override
        public void run() {
            this.isRunning = true;
            while (this.isRunning) {
                if (timeout != -1 && XdagTime.getCurrentTimestamp() > timeout) {
                    log.debug("CurrentTimestamp:{},sendTime:{} Timeout!", XdagTime.getCurrentTimestamp(), timeout);
                    timeout = -1;
                    events.add(new Event(Event.Type.TIMEOUT));
                    continue;
                }
                try {
                    Thread.sleep(10);
                } catch (InterruptedException e) {
                    log.error(e.getMessage(), e);
                }
            }
        }

        public void timeout(long sendtime) {
            if (sendtime < 0) {
                throw new IllegalArgumentException("Timeout can not be negative");
            }
            this.timeout = sendtime;
        }
    }

    public class Broadcaster implements Runnable {
        private final LinkedBlockingQueue<BlockWrapper> queue = new LinkedBlockingQueue<>();
        private volatile boolean isRunning = false;

        @Override
        public void run() {
            isRunning = true;
            while (isRunning) {
                BlockWrapper bw = null;
                try {
                    bw = queue.poll(50, TimeUnit.MILLISECONDS);
                } catch (InterruptedException e) {
                    log.error(e.getMessage(), e);
                }
                if (bw != null) {
                    channelMgr.sendNewBlock(bw);
                }
            }
        }

        public void broadcast(BlockWrapper bw) {
            if (!queue.offer(bw)) {
                log.error("Failed to add a message to the broadcast queue: block = {}", bw.getBlock()
                        .getHash().toHexString());
            }
        }
    }

    public class GetShares implements Runnable {

        private boolean isRunning = false;
        private static final int SHARE_FLAG = 2;

        @Override
        public void run() {
            isRunning = true;
            while (isRunning) {
                String shareInfo = null;
                try {
                    shareInfo = shareQueue.poll(50, TimeUnit.MILLISECONDS);
                } catch (InterruptedException e) {
                    log.error(e.getMessage(), e);
                }
                if (shareInfo != null) {
                    try {
                        Random random = new Random();
                        JSONObject shareJson = new JSONObject(shareInfo);
                        if (shareJson.getInt("msgType") == SHARE_FLAG) {
                            receiveNewShare(shareJson.getJSONObject("msgContent").getString("share"),
                                    shareJson.getJSONObject("msgContent").getString("hash"),
                                    shareJson.getJSONObject("msgContent").getLong("taskIndex"),
                                    shareJson.getJSONObject("msgContent").has("poolTag") ? shareJson.getJSONObject(
                                            "msgContent").getString("poolTag") : "NULL POOL" + random.nextInt(1000));
                        } else {
                            log.error("Share format error! Current share: {}", shareInfo);
                        }

                    } catch (JSONException e) {
                        log.error("Share format error, current share: {}", shareInfo);
                    }
                }
                if (isSetMinShare) {
                    // pool last hash
                    Bytes32StringPair poolInfo = threadMinHash.get();
                    try {
                        setNonce(poolInfo.getValue(), poolInfo.getKey());
                    } catch (IOException e) {
                        throw new RuntimeException(e);
                    }
                    //init last hash
                    poolInfo.setKey(Bytes32.fromHexString("ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"));
                    poolInfo.setValue("NULL");
                }
            }
        }
    }

    private static class Bytes32StringPair {
        private Bytes32 key;
        private String value;

        public Bytes32StringPair(Bytes32 key, String value) {
            this.key = key;
            this.value = value;
        }

        public Bytes32 getKey() {
            return key;
        }

        public void setKey(Bytes32 key) {
            this.key = key;
        }

        public String getValue() {
            return value;
        }

        public void setValue(String value) {
            this.value = value;
        }
    }


    public void getShareInfo(String share) {
        if (!shareQueue.offer(share)) {
            log.error("Failed to get ShareInfo from pools");
        }
    }
}
