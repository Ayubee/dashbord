# Davomat dashboard — bulut (Railway) uchun.
# Ma'lumotlar /data ga yoziladi: Railway'da shu yo'lga Volume ulang, aks holda har deploy'da o'chadi.
FROM python:3.12-slim

RUN apt-get update && apt-get install -y --no-install-recommends tzdata \
    && ln -sf /usr/share/zoneinfo/Asia/Tashkent /etc/localtime \
    && echo "Asia/Tashkent" > /etc/timezone \
    && rm -rf /var/lib/apt/lists/*

ENV PYTHONUNBUFFERED=1 \
    TZ=Asia/Tashkent \
    DATA_DIR=/data

WORKDIR /app
COPY server.py ./
COPY web ./web

CMD ["python", "server.py", "--no-browser"]
